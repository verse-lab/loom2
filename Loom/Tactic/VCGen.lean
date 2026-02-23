import Lean
import Loom.Tactic.Attr
import Loom.Triple.Basic
import Loom.Triple.SpecLemmas
import Loom.WP.SimpLemmas
import Lean.Meta
import Lean.Meta.Match.Rewrite

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
TODO:
  - Transform Triple to ⊑ at @[lspec] level
  - add abstraction over `post` and `epost`

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
  (l instWP : Expr) (excessArgs : Array Expr) : OptionT SymM BackwardRule := do
  -- dbg_trace s!"tryMkBackwardRuleFromSpec: instWP = {← ppExpr instWP}"
  -- Instantiate the spec theorem, creating metavars for all universally quantified params
  let (_xs, _bs, specProof, specType) ← specThm.proof.instantiate
  let_expr PartialOrder.rel l' _cl' pre rhs := specType
    | throwError "target not a partial order ⊑ application {specType}"
  -- Use isDefEqGuarded (not isDefEqS) because isDefEqS is a lightweight structural check
  -- that may fail to see through abbreviations like `Unit := PUnit`
  guard <| ← isDefEqGuarded l l'
  let_expr wp _m' _ _e' _monadInst' _cl' _ce' instWP' _α _prog _post _epost := rhs
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

open Lean.Elab.Tactic.Do in
/--
Creates a reusable backward rule for `ite`. It proves a theorem of the following form:
```
example {m} {σ} {l} {e} [WPMonad m l e] -- These are fixed. The other arguments are parameters of the rule:
  {α} {c : Prop} [Decidable c] {t e : m α} {s₁ s₂ ... : σ} {pre : l} {post : α → l} {epost : e}
  (hthen : wp t post epost s₁ s₂ ...) (helse : wp e post epost s₁ s₂ ...)
  : wp (ite c t e) post epost s₁ s₂ ...
```
-/
meta def mkBackwardRuleForIte
    (wpHead m l errTy monadInst cl ce instWP : Expr)
    (excessArgs : Array Expr) : SymM BackwardRule := do
  let mTy ← Sym.inferType m
  let some aTy := if mTy.isForall then some mTy.bindingDomain! else none
    | throwError "Expected monad type constructor at {indentExpr m}"
  let prf ← withLocalDeclD `a aTy fun a => do
    let ma ← shareCommon <| mkApp m a
    withLocalDeclD `c (mkSort 0) fun c => do
    withLocalDeclD `dec (mkApp (mkConst ``Decidable) c) fun dec => do
    withLocalDeclD `t ma fun t => do
    withLocalDeclD `e ma fun e => do
    let maTy ← Sym.inferType ma
    let v ←
      match maTy with
      | .sort lvl => pure lvl
      | _ => throwError "Expected sort for type {indentExpr maTy}"
    let prog ← shareCommon (mkApp5 (mkConst ``ite [v]) ma c dec t e)
    let excessArgNamesTypes ← excessArgs.mapM fun arg =>
      return (`s, ← Sym.inferType arg)
    withLocalDeclsDND excessArgNamesTypes fun ss => do
    withLocalDeclD `post (← shareCommon (← mkArrow a l)) fun post => do
    withLocalDeclD `epost errTy fun epost => do
    let goalWithProg (prog : Expr) :=
      mkAppN (mkAppN wpHead #[m, l, errTy, monadInst, cl, ce, instWP, a, prog, post, epost]) ss
    let thenType ← mkArrow c (goalWithProg t)
    withLocalDeclD `hthen (← shareCommon thenType) fun hthen => do
    let elseType ← mkArrow (mkNot c) (goalWithProg e)
    withLocalDeclD `helse (← shareCommon elseType) fun helse => do
    let onAlt (hc : Expr) (hcase : Expr) := do
      let res ← rwIfWith hc prog
      if res.proof?.isNone then
        throwError "`rwIfWith` failed to rewrite {indentExpr prog}."
      let context ← withLocalDecl `x .default ma fun x => mkLambdaFVars #[x] (goalWithProg x)
      let res ← Simp.mkCongrArg context res
      res.mkEqMPR hcase
    let ht ← withLocalDecl `h .default c fun h => do
      mkLambdaFVars #[h] (← onAlt h (mkApp hthen h))
    let he ← withLocalDecl `h .default (mkNot c) fun h => do
      mkLambdaFVars #[h] (← onAlt h (mkApp helse h))
    let goalTy := goalWithProg prog
    let goalTySort ← Sym.inferType goalTy
    let u ←
      match goalTySort with
      | .sort lvl => pure lvl
      | _ => throwError "Expected sort for type {indentExpr goalTySort}"
    let prf := mkApp5 (mkConst ``dite [u]) goalTy c dec ht he
    mkLambdaFVars (#[a, c, dec, t, e] ++ ss ++ #[post, epost, hthen, helse]) prf
  let res ← abstractMVars prf
  let type ← preprocessExpr (← Sym.inferType res.expr)
  let prf ← Meta.mkAuxLemma res.paramNames.toList type res.expr
  mkBackwardRuleFromDecl prf

/--
Given an array of `SpecTheorem`s (sorted by priority), try to build a backward rule
from the first matching spec.

The backward rule is an auxiliary lemma with excess state arguments made explicit:
for `l = σ1 → ... → σn → Prop`, it turns `pre ⊑ wp x post epost` into
`∀ s1 ... sn, pre s1 ... sn → wp x post epost s1 ... sn`.
-/
def mkBackwardRuleFromSpecs (specThms : Array SpecTheorem)
    (l instWP : Expr) (excessArgs : Array Expr)
    : MetaM (Option (SpecTheorem × BackwardRule)) := SymM.run do
  for specThm in specThms do
    if let some rule ← withNewMCtxDepth
        (tryMkBackwardRuleFromSpec specThm l instWP excessArgs) then
      return (specThm, rule)
  return none

/-! ## VCGen monad and caching -/

structure VCGen.Context where
  specThms : SpecTheorems
  -- TODO: entailsConsIntroRule : BackwardRule

structure VCGen.State where
  /-- Cache mapping spec theorem names × WPMonad instance × excess arg count
      to their backward rule. Avoids rebuilding the same aux lemma repeatedly. -/
  specBackwardRuleCache : Std.HashMap (Array Name × Expr × Nat) (SpecTheorem × BackwardRule) := {}
  /-- Cache mapping split rule name × WPMonad instance × excess arg count
      to their backward rule. -/
  splitBackwardRuleCache : Std.HashMap (Name × Expr × Nat) BackwardRule := {}
  /-- Holes of type `Invariant` generated so far. -/
  invariants : Array MVarId := #[]
  /-- Verification conditions generated so far. -/
  vcs : Array MVarId := #[]

abbrev VCGenM := ReaderT VCGen.Context (StateRefT VCGen.State SymM)

namespace VCGen

def SpecTheorem.global? (specThm : SpecTheorem) : Option Name :=
  match specThm.proof with | .global decl => some decl | _ => none

/-- Cached version of `mkBackwardRuleFromSpecs`. The cache key is
    `(spec decl names, instWP, excessArgs.size)`. Falls back to the uncached
    version when any spec theorem is not a global declaration. -/
def mkBackwardRuleFromSpecsCached (specThms : Array SpecTheorem)
    (l instWP : Expr) (excessArgs : Array Expr)
    : OptionT VCGenM (SpecTheorem × BackwardRule) := do
    let decls := specThms.filterMap SpecTheorem.global?
    let s := (← get).specBackwardRuleCache
    match s[(decls, instWP, excessArgs.size)]? with
    | some (specThm, rule) => return (specThm, rule)
    | none =>
      let some rule ← mkBackwardRuleFromSpecs specThms l instWP excessArgs
        | failure
      let key := (decls, instWP, excessArgs.size)
      modify ({ · with specBackwardRuleCache := s.insert key rule })
      return rule

/-- Cached wrapper for `mkBackwardRuleForIte`. -/
def mkBackwardRuleForIteCached
    (wpHead m l errTy monadInst cl ce instWP : Expr)
    (excessArgs : Array Expr) : VCGenM BackwardRule := do
  let s := (← get).splitBackwardRuleCache
  match s[(``ite, instWP, excessArgs.size)]? with
  | some rule => return rule
  | none =>
    let rule ← mkBackwardRuleForIte wpHead m l errTy monadInst cl ce instWP excessArgs
    let key := (``ite, instWP, excessArgs.size)
    modify ({ · with splitBackwardRuleCache := s.insert key rule })
    return rule

inductive SolveResult where
  /-- The `T` was not of the form `wp e post epost s₁ ... sₙ`. -/
  | noProgramFoundInTarget (T : Expr)
  /-- Don't know how to handle `e` in `wp e post epost s₁ ... sₙ`. -/
  | noStrategyForProgram (e : Expr)
  /--
  Did not find a spec for the `e` in `wp e post epost s₁ ... sₙ`.
  Candidates were `thms`, but none of them matched the monad.
  -/
  | noSpecFoundForProgram (e : Expr) (monad : Expr) (thms : Array SpecTheorem)
  /-- Successfully discharged the goal. These are the subgoals. -/
  | goals (subgoals : List MVarId)


def solve (goal : MVarId) : VCGenM SolveResult := goal.withContext do
  let target ← goal.getType
  -- Goal should be: @WPMonad.wp m l errTy monadInst cl ce instWP α e post epost s₁ ... sₙ
  -- WPMonad.wp has 11 base args; anything beyond that are excess state args
  target.withApp fun head args => do
    let_expr wp m l errTy monadInst cl ce instWP _α e _post _epost :=
      mkAppN head (args.extract 0 (min args.size 11))
      | return .noProgramFoundInTarget target
    let excessArgs := args.extract 11 args.size
    -- Non-dependent let-expressions: use Sym.Simp.simpLet to preserve maximal sharing
    -- TODO: is it the best way?
    if e.isLet then
      if let .step e' .. ← Simp.SimpM.run' (Simp.simpLet e) then
        let target' ← share <| mkAppN head (args.set! 8 e')
        return .goals [← goal.replaceTargetDefEq target']
      else return .noStrategyForProgram e
    -- Apply registered specifications
    let f := e.getAppFn
    if f.isConstOf ``ite || f.isAppOf ``ite then
      let rule ← mkBackwardRuleForIteCached head m l errTy monadInst cl ce instWP excessArgs
      let .goals goals ← rule.apply goal
        | throwError "Failed to apply split rule for {indentExpr e}"
      return .goals goals
    if f.isConst || f.isFVar then
      let thms ← (← read).specThms.findSpecs e
      let some (_, rule) ← (mkBackwardRuleFromSpecsCached thms l instWP excessArgs).run
        | return .noSpecFoundForProgram e m thms
      let .goals goals ← rule.apply goal
        | throwError "Failed to apply rule for {indentExpr e}"
      return .goals goals
    return .noStrategyForProgram e

/--
Called when decomposing the goal further did not succeed; in this case we emit a VC for the goal.
-/
meta def emitVC (goal : MVarId) : VCGenM Unit := do
  let ty ← goal.getType
  goal.setKind .syntheticOpaque
  if ty.isAppOf ``Std.Do.Invariant then
    modify fun s => { s with invariants := s.invariants.push goal }
  else
    modify fun s => { s with vcs := s.vcs.push goal }

/-- Unfold `⦃P⦄ x ⦃Q⦄` into `P ⊢ₛ wp⟦x⟧ Q`. -/
meta def unfoldTriple (goal : MVarId) : OptionT SymM MVarId := goal.withContext do
  let type ← goal.getType
  unless type.isAppOf ``Triple do return goal
  let simpTripleMethod <- mkMethods #[``Triple.iff]
  let (res, _) ← Simp.SimpM.run (simpGoal (methods := simpTripleMethod) goal)
  match res with
  | .goal goal => return goal
  | .closed => failure
  | .noProgress => return goal

def introsWP (goal : MVarId) : SymM MVarId := do
  let mut goal := goal
  if (← goal.getType).isForall then
    let IntrosResult.goal _ goal' ← Sym.intros goal | failure
    goal := goal'
  return goal

meta def work (goal : MVarId) : VCGenM Unit := do
  let goal ← preprocessMVar goal
  let some goal ← unfoldTriple goal |>.run | return ()
  let mut worklist := Std.Queue.empty.enqueue goal
  repeat do
    let some (goal, worklist') := worklist.dequeue? | break
    worklist := worklist'
    let res ← solve =<< introsWP goal
    match res with
    | .noProgramFoundInTarget .. =>
      emitVC goal
    | .noSpecFoundForProgram prog _ #[] =>
      throwError "No spec found for program {prog}."
    | .noSpecFoundForProgram prog monad thms =>
      throwError "No spec matching the monad {monad} found for program {prog}. Candidates were {thms.map (·.proof)}."
    | .noStrategyForProgram prog =>
      throwError "Did not know how to decompose weakest precondition for {prog}"
    | .goals subgoals =>
      worklist := worklist.enqueueAll subgoals

public structure Result where
  invariants : Array MVarId
  vcs : Array MVarId

/--
Generate verification conditions for a goal of the form `Triple pre e s₁ ... sₙ` by repeatedly
decomposing `e` using registered `@[spec]` theorems.
Return the VCs and invariant goals.
-/
public meta partial def main (goal : MVarId) (ctx : Context) : SymM Result := do
  let ((), state) ← StateRefT'.run (ReaderT.run (work goal) ctx) {}
  for h : idx in [:state.invariants.size] do
    let mv := state.invariants[idx]
    mv.setTag (Name.mkSimple ("inv" ++ toString (idx + 1)))
  for h : idx in [:state.vcs.size] do
    let mv := state.vcs[idx]
    mv.setTag (Name.mkSimple ("vc" ++ toString (idx + 1)) ++ (← mv.getTag).eraseMacroScopes)
  return { invariants := state.invariants, vcs := state.vcs }


syntax (name := mvcgen') "mvcgen'"
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "] ")? : tactic

@[tactic mvcgen']
public meta def elabMVCGen' : Tactic := fun _stx => withMainContext do
  let ctx ← getSpecTheorems
  let goal ← getMainGoal
  let { invariants, vcs } ← SymM.run <| VCGen.main goal ⟨ctx⟩
  replaceMainGoal (invariants ++ vcs).toList


end VCGen

section Test

/-- Test helper: create a SpecTheorem from a declaration and run tryMkBackwardRuleFromSpec
    with the given monad type expressions. Returns the type of the auxiliary lemma. -/
def testBackwardRule (declName : Name) (l instWP : Expr)
    (excessArgs : Array Expr) : MetaM Expr := do
  let specThm ← mkSpecTheoremFromConst declName
  let rule ← SymM.run do
    tryMkBackwardRuleFromSpec specThm l instWP excessArgs
  match rule with
  | some br => inferType br.expr
  | none => throwError "tryMkBackwardRuleFromSpec returned none for {declName}"

/-- Test helper: run `mkBackwardRuleForIte` with the given monad/lattice expressions.
    Returns the type of the generated auxiliary lemma. -/
def testIteBackwardRule
    (wpHead m l errTy monadInst cl ce instWP : Expr)
    (excessArgs : Array Expr) : MetaM Expr := do
  let rule ← SymM.run do
    mkBackwardRuleForIte wpHead m l errTy monadInst cl ce instWP excessArgs
  inferType rule.expr

-- Test 1: Id monad, l = Prop, n = 0 excess args
-- wp_bind for Id: pre → wp (x >>= f) post ()
#eval show MetaM Unit from do
  let m := mkConst ``Id [.zero]
  let l := mkSort 0
  let e := mkConst ``EPost.nil
  let cl ← synthInstance (← mkAppM ``CompleteLattice #[l])
  let ce ← synthInstance (← mkAppM ``CompleteLattice #[e])
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero]) #[m, l, e, monadM, cl, ce])
  let ty ← testBackwardRule ``WPMonad.wp_bind l instWP #[]
  logInfo m!"Test 1 (Id, n=0): {ty}"

-- Test 2: StateM Nat, l = Nat → Prop, n = 1 excess arg
-- wp_bind for StateM Nat: ∀ s, pre s → wp (x >>= f) post () s
#eval show MetaM Unit from do
  let nat := mkConst ``Nat
  let m ← mkAppM ``StateM #[nat]
  let l ← mkArrow nat (mkSort 0)
  let e := mkConst ``EPost.nil
  let cl ← synthInstance (← mkAppM ``CompleteLattice #[l])
  let ce ← synthInstance (← mkAppM ``CompleteLattice #[e])
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero]) #[m, l, e, monadM, cl, ce])
  withLocalDeclD `s nat fun s => do
    let ty ← testBackwardRule ``WPMonad.wp_bind l instWP #[s]
    logInfo m!"Test 2 (StateM Nat, n=1): {ty}"

-- Test 3: get for StateM Nat, n = 1 excess arg
-- Spec.get_StateT': ∀ s, (fun s => post s s) s → wp get post epost s
@[lspec] theorem spec_get_StateT {m : Type u → Type v} {l e : Type u}
    [CompleteLattice l] [CompleteLattice e] [Monad m] [LawfulMonad m] [WPMonad m l e]
    {σ : Type u} (post : σ → σ → l) (epost : e) :
    (fun s => post s s) ⊑ wp (MonadStateOf.get : StateT σ m σ) post epost := by
  exact WP.get_StateT_wp post epost

#eval show MetaM Unit from do
  let nat := mkConst ``Nat
  let m ← mkAppM ``StateM #[nat]
  let l ← mkArrow nat (mkSort 0)
  let e := mkConst ``EPost.nil
  let cl ← synthInstance (← mkAppM ``CompleteLattice #[l])
  let ce ← synthInstance (← mkAppM ``CompleteLattice #[e])
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero]) #[m, l, e, monadM, cl, ce])
  withLocalDeclD `s nat fun s => do
    let ty ← testBackwardRule ``spec_get_StateT l instWP #[s]
    logInfo m!"Test 3 (get StateM Nat, n=1): {ty}"

-- Test 4: ite for StateM Nat, n = 1 excess arg
-- mkBackwardRuleForIte:
--   ∀ s, (c → wp t post epost s) → (¬c → wp e post epost s) → wp (ite c t e) post epost s
#eval show MetaM Unit from do
  let nat := mkConst ``Nat
  let m ← mkAppM ``StateM #[nat]
  let l ← mkArrow nat (mkSort 0)
  let errTy := mkConst ``EPost.nil
  let cl ← synthInstance (← mkAppM ``CompleteLattice #[l])
  let ce ← synthInstance (← mkAppM ``CompleteLattice #[errTy])
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance
    (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero]) #[m, l, errTy, monadM, cl, ce])
  let wpHead := mkConst ``wp [.zero, .zero, .zero]
  withLocalDeclD `s nat fun s => do
    let ty ← testIteBackwardRule wpHead m l errTy monadM cl ce instWP #[s]
    logInfo m!"Test 4 (ite StateM Nat, n=1): {ty}"

-- Test 5: ite for Id, n = 0 excess args
#eval show MetaM Unit from do
  let m := mkConst ``Id [.zero]
  let l := mkSort 0
  let errTy := mkConst ``EPost.nil
  let cl ← synthInstance (← mkAppM ``CompleteLattice #[l])
  let ce ← synthInstance (← mkAppM ``CompleteLattice #[errTy])
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance
    (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero]) #[m, l, errTy, monadM, cl, ce])
  let wpHead := mkConst ``wp [.zero, .zero, .zero]
  let ty ← testIteBackwardRule wpHead m l errTy monadM cl ce instWP #[]
  logInfo m!"Test 5 (ite Id, n=0): {ty}"

namespace MTest
section
abbrev M := ExceptT String <| ReaderT String <| ExceptT Nat <| StateT Nat <| ExceptT Unit <| StateM Unit

@[local lspec]
theorem Spec.M_getThe_Nat :
  (fun s₁ s₂ => post s₂ s₁ s₂) ⊑ wp (get (σ := Nat) (m := M)) post epost := by
  sorry

#eval show MetaM Unit from do
  let string := mkConst ``String
  let nat := mkConst ``Nat
  let unit := mkConst ``Unit
  let m := mkConst ``M
  let l ← mkArrow string (← mkArrow nat (← mkArrow unit (mkSort 0)))
  let e1 ← mkArrow string (← mkArrow string (← mkArrow nat (← mkArrow unit (mkSort 0))))
  let e2 ← mkArrow nat (← mkArrow nat (← mkArrow unit (mkSort 0)))
  let e3 ← mkArrow unit (← mkArrow unit (mkSort 0))
  let enil := mkConst ``EPost.nil
  let e34 ← mkAppM ``EPost.cons #[e3, enil]
  let e234 ← mkAppM ``EPost.cons #[e2, e34]
  let e ← mkAppM ``EPost.cons #[e1, e234]
  let cl ← synthInstance (← mkAppM ``CompleteLattice #[l])
  let ce ← synthInstance (← mkAppM ``CompleteLattice #[e])
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero]) #[m, l, e, monadM, cl, ce])
  withLocalDeclD `s₁ string fun s₁ => do
    withLocalDeclD `s₂ nat fun s₂ => do
      withLocalDeclD `s₃ unit fun s₃ => do
        let ty ← testBackwardRule ``Spec.M_getThe_Nat l instWP #[s₁, s₂, s₃]
        logInfo m!"Test 6 (Spec.M_getThe_Nat): {ty}"

-- Test 7: ite for deep M, n = 3 excess args
#eval show MetaM Unit from do
  let string := mkConst ``String
  let nat := mkConst ``Nat
  let unit := mkConst ``Unit
  let m := mkConst ``M
  let l ← mkArrow string (← mkArrow nat (← mkArrow unit (mkSort 0)))
  let e1 ← mkArrow string (← mkArrow string (← mkArrow nat (← mkArrow unit (mkSort 0))))
  let e2 ← mkArrow nat (← mkArrow nat (← mkArrow unit (mkSort 0)))
  let e3 ← mkArrow unit (← mkArrow unit (mkSort 0))
  let enil := mkConst ``EPost.nil
  let e34 ← mkAppM ``EPost.cons #[e3, enil]
  let e234 ← mkAppM ``EPost.cons #[e2, e34]
  let errTy ← mkAppM ``EPost.cons #[e1, e234]
  let cl ← synthInstance (← mkAppM ``CompleteLattice #[l])
  let ce ← synthInstance (← mkAppM ``CompleteLattice #[errTy])
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance
    (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero]) #[m, l, errTy, monadM, cl, ce])
  let wpHead := mkConst ``wp [.zero, .zero, .zero]
  withLocalDeclD `s₁ string fun s₁ => do
    withLocalDeclD `s₂ nat fun s₂ => do
      withLocalDeclD `s₃ unit fun s₃ => do
        let ty ← testIteBackwardRule wpHead m l errTy monadM cl ce instWP #[s₁, s₂, s₃]
        logInfo m!"Test 7 (ite M, n=3): {ty}"


-- @[lspec] theorem spec_set_StateT {m : Type u → Type v} {l e : Type u}
--     [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e]
--     {σ : Type u} (x : σ) (post : PUnit → σ → l) (epost : e) :
--     (fun _ => post ⟨⟩ x) ⊑ wp (MonadStateOf.set x : StateT σ m PUnit) post epost := by
--   exact WP.set_StateT_wp x post epost

end
end MTest
end Test

end Loom
