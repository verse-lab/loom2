import Lean
import Loom.Tactic.Attr
import Loom.Triple.Basic
import Loom.Triple.SpecLemmas
import Loom.WP.SimpLemmas
import Lean.Meta

open Lean Parser Meta Elab Tactic Sym Loom Lean.Order
open Loom.Tactic.SpecAttr

namespace Loom

namespace Loom.Tactic.SpecAttr

/--
Look up `SpecTheorem`s in the `@[lspec]` database.
Takes all specs that match the given program `e` and sorts by descending priority.
-/
def SpecTheorems.findSpecs (database : SpecTheorems) (e : Expr) : MetaM (Array SpecTheorem) := do
  let candidates ← database.specs.getMatch e
  let candidates := candidates.filter (!database.erased.contains ·.proof)
  return candidates.qsort (·.priority > ·.priority)

end Loom.Tactic.SpecAttr

/-- Count function arrows in a type, e.g. `σ1 → σ2 → Prop` → 2 -/
private partial def countExcessArgs (l : Expr) : MetaM Nat := do
  let l ← whnfR l
  if l.isForall then return 1 + (← countExcessArgs l.bindingBody!)
  else return 0

/-- Extract the argument types from function arrows of a type -/
private def getExcessArgTypes (l : Expr) (n : Nat) : MetaM (Array Expr) := do
  let mut result := #[]
  let mut l := l
  for _ in [:n] do
    l ← whnfR l
    result := result.push l.bindingDomain!
    l := l.bindingBody!
  return result

def preprocessExpr (e : Expr) : SymM Expr := do
  shareCommon (← unfoldReducible (← instantiateMVars e))


/--
Try to build a backward rule from a single spec theorem in `⊑` form.

Given a spec `pre ⊑ wp prog post epost` where the lattice type is
`l = σ1 → ... → σn → Prop`, produces an auxiliary lemma of the form
`∀ s1 ... sn, pre s1 ... sn → wp prog post epost s1 ... sn`.

This conversion is necessary because `PartialOrder.rel` is a projection (not unfolded
by `unfoldReducible`), so `mkPatternFromType` cannot structurally see the `→`. We
explicitly construct the `→` type via `mkExpectedTypeHint`.

- `l`: the goal's lattice type (e.g. `Nat → Prop`)
- `instWP`: the `WPMonad` instance for the goal monad; matching against the spec's
  instance transitively unifies `m`, `e`, `cl`, and `monadInst`
- `excessArgs`: free variables representing state args from `l = σ1 → ... → σn → Prop`;
  fresh metavariables are created for these so that `abstractMVars` can abstract them
  alongside the spec's universally quantified parameters
-/
def tryMkBackwardRuleFromSpec (specThm : SpecTheorem)
  (l _monadInst instWP : Expr) (excessArgs : Array Expr) : OptionT SymM BackwardRule := do
  -- Instantiate the spec theorem, creating metavars for all universally quantified params
  let (_xs, _bs, specProof, specType) ← specThm.proof.instantiate
  -- Match: pre ⊑ rhs
  let_expr PartialOrder.rel l' _cl' pre rhs := specType
    | throwError "target not a partial order ⊑ application {specType}"
  -- Ensure the spec's lattice type matches the goal's (e.g. both `Nat → Prop`)
  guard <| ← isDefEqS l l'
  -- Match: rhs = wp prog post epost (and unify instances via instWP)
  let_expr wp _m' _ _e' _monadInst' _cl' instWP' _α _prog _post _epost := rhs
    | throwError "target not a wp application {rhs}"
  -- Unifying instWP transitively assigns m, e, cl, monadInst via type-level unification
  guard <| ← isDefEqGuarded instWP instWP'
  -- Create fresh metavars for excess state args (abstractMVars will bind them as ∀)
  let ss ← excessArgs.mapM fun arg => do
    mkFreshExprMVar (userName := `s) <| ← Sym.inferType arg
  -- Build: pre s1 ... sn → wp prog post epost s1 ... sn
  -- Using mkExpectedTypeHint because PartialOrder.rel is a projection that
  -- unfoldReducible/mkPatternFromType cannot see through structurally
  let proofType ← mkArrow (mkAppN pre ss) (mkAppN rhs ss)
  let spec ← mkExpectedTypeHint (mkAppN specProof ss) proofType
  -- Abstract all remaining metavars (spec params + excess args) into an aux lemma
  let res ← abstractMVars spec
  let type ← preprocessExpr (← Sym.inferType res.expr)
  let spec ← Meta.mkAuxLemma res.paramNames.toList type res.expr
  mkBackwardRuleFromDecl spec

/--
Given an array of `SpecTheorem`s (sorted by priority), try to build a backward rule
from the first matching spec.

The backward rule is an auxiliary lemma with excess state arguments made explicit:
for `l = σ1 → ... → σn → Prop`, it turns `pre ⊑ wp x post epost` into
`∀ s1 ... sn, pre s1 ... sn → wp x post epost s1 ... sn`.
-/
def mkBackwardRuleFromSpecs (specThms : Array SpecTheorem)
    (l monadInst instWP : Expr) (excessArgs : Array Expr)
    : MetaM (Option (SpecTheorem × BackwardRule)) := SymM.run do
  for specThm in specThms do
    if let some rule ← withNewMCtxDepth
        (tryMkBackwardRuleFromSpec specThm l monadInst instWP excessArgs) then
      return (specThm, rule)
  return none

section Test

/-- Test helper: create a SpecTheorem from a declaration and run tryMkBackwardRuleFromSpec
    with the given monad type expressions. Returns the type of the auxiliary lemma. -/
def testBackwardRule (declName : Name) (l monadInst instWP : Expr)
    (excessArgs : Array Expr) : MetaM Expr := do
  let specThm ← mkSpecTheoremFromConst declName
  let rule ← SymM.run do
    tryMkBackwardRuleFromSpec specThm l monadInst instWP excessArgs
  match rule with
  | some br => inferType br.expr
  | none => throwError "tryMkBackwardRuleFromSpec returned none for {declName}"

-- Test 1: Id monad, l = Prop, n = 0 excess args
-- wp_bind for Id: pre → wp (x >>= f) post ()
#eval show MetaM Unit from do
  let m := mkConst ``Id [.zero]
  let l := mkSort 0
  let e := mkConst ``Unit
  let cl ← synthInstance (← mkAppM ``CompleteLattice #[l])
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero]) #[m, l, e, monadM, cl])
  let ty ← testBackwardRule ``WPMonad.wp_bind l monadM instWP #[]
  logInfo m!"Test 1 (Id, n=0): {ty}"

-- Test 2: StateM Nat, l = Nat → Prop, n = 1 excess arg
-- wp_bind for StateM Nat: ∀ s, pre s → wp (x >>= f) post () s
#eval show MetaM Unit from do
  let nat := mkConst ``Nat
  let m ← mkAppM ``StateM #[nat]
  let l ← mkArrow nat (mkSort 0)
  let e := mkConst ``Unit
  let cl ← synthInstance (← mkAppM ``CompleteLattice #[l])
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero]) #[m, l, e, monadM, cl])
  withLocalDeclD `s nat fun s => do
    let ty ← testBackwardRule ``WPMonad.wp_bind l monadM instWP #[s]
    logInfo m!"Test 2 (StateM Nat, n=1): {ty}"

-- Test 3: get for StateM Nat, n = 1 excess arg
-- Spec.get_StateT': ∀ s, (fun s => post s s) s → wp get post epost s
theorem spec_get_StateT {m : Type u → Type v} {l e : Type u}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e]
    {σ : Type u} (post : σ → σ → l) (epost : e) :
    (fun s => post s s) ⊑ wp (MonadStateOf.get : StateT σ m σ) post epost := by
  rw [WP.get_StateT_wp]

#eval show MetaM Unit from do
  let nat := mkConst ``Nat
  let m ← mkAppM ``StateM #[nat]
  let l ← mkArrow nat (mkSort 0)
  let e := mkConst ``Unit
  let cl ← synthInstance (← mkAppM ``CompleteLattice #[l])
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero]) #[m, l, e, monadM, cl])
  withLocalDeclD `s nat fun s => do
    let ty ← testBackwardRule ``spec_get_StateT l monadM instWP #[s]
    logInfo m!"Test 3 (get StateM Nat, n=1): {ty}"

end Test

end Loom
