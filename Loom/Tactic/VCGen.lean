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
  (l _monadInst instWP : Expr) (excessArgs : Array Expr) : OptionT SymM BackwardRule := do
  -- Instantiate the spec theorem, creating metavars for all universally quantified params
  let (_xs, _bs, specProof, specType) ← specThm.proof.instantiate
  let_expr PartialOrder.rel l' _cl' pre rhs := specType
    | throwError "target not a partial order ⊑ application {specType}"
  guard <| ← isDefEqS l l' -- Ensure the spec's lattice type matches the goal's (e.g. both `Nat → Prop`)
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

/-! ## VCGen monad and caching -/

structure VCGen.Context where
  specThms : SpecTheorems
  -- TODO: entailsConsIntroRule : BackwardRule

structure VCGen.State where
  /-- Cache mapping spec theorem names × WPMonad instance × excess arg count
      to their backward rule. Avoids rebuilding the same aux lemma repeatedly. -/
  specBackwardRuleCache : Std.HashMap (Array Name × Expr × Nat) (SpecTheorem × BackwardRule) := {}
  /-- Holes of type `Invariant` generated so far. -/
  invariants : Array MVarId := #[]
  /-- Verification conditions generated so far. -/
  vcs : Array MVarId := #[]

abbrev VCGenM := ReaderT VCGen.Context (StateRefT VCGen.State SymM)

namespace VCGen

@[inline] def _root_.Std.HashMap.getDM [Monad m] [BEq α] [Hashable α]
    (cache : Std.HashMap α β) (key : α) (fallback : m β) : m (β × Std.HashMap α β) := do
  if let some b := cache.get? key then
    return (b, cache)
  let b ← fallback
  return (b, cache.insert key b)

def SpecTheorem.global? (specThm : SpecTheorem) : Option Name :=
  match specThm.proof with | .global decl => some decl | _ => none

/-- Cached version of `mkBackwardRuleFromSpecs`. The cache key is
    `(spec decl names, instWP, excessArgs.size)`. Falls back to the uncached
    version when any spec theorem is not a global declaration. -/
def mkBackwardRuleFromSpecsCached (specThms : Array SpecTheorem)
    (l monadInst instWP : Expr) (excessArgs : Array Expr)
    : OptionT VCGenM (SpecTheorem × BackwardRule) := do
    let decls := specThms.filterMap SpecTheorem.global?
    let s := (← get).specBackwardRuleCache
    match s[(decls, instWP, excessArgs.size)]? with
    | some (specThm, rule) => return (specThm, rule)
    | none =>
      let some rule ← mkBackwardRuleFromSpecs specThms l monadInst instWP excessArgs
        | failure
      let key := (decls, instWP, excessArgs.size)
      modify ({ · with specBackwardRuleCache := s.insert key rule })
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
  -- Goal should be: @WPMonad.wp m l errTy monadInst cl instWP α e post epost s₁ ... sₙ
  -- WPMonad.wp has 10 base args; anything beyond that are excess state args
  target.withApp fun head args => do
    let_expr wp _m l _errTy monadInst _cl instWP _α e _post _epost :=
      mkAppN head (args.extract 0 (min args.size 10))
      | return .noProgramFoundInTarget target
    let excessArgs := args.extract 10 args.size
    -- Non-dependent let-expressions: use Sym.Simp.simpLet to preserve maximal sharing
    -- TODO: is it the best way?
    if e.isLet then
      if let .step e' .. ← Simp.SimpM.run' (Simp.simpLet e) then
        let target' ← share <| mkAppN head (args.set! 7 e')
        return .goals [← goal.replaceTargetDefEq target']
      else return .noStrategyForProgram e
    -- Apply registered specifications
    let f := e.getAppFn
    if f.isConst || f.isFVar then
      let thms ← (← read).specThms.findSpecs e
      let some (_, rule) ← (mkBackwardRuleFromSpecsCached thms l monadInst instWP excessArgs).run
        | return .noSpecFoundForProgram e monadInst thms
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

meta def work (goal : MVarId) : VCGenM Unit := do
  let goal ← preprocessMVar goal
  let some goal ← unfoldTriple goal |>.run | return ()
  let mut worklist := Std.Queue.empty.enqueue goal
  repeat do
    let some (goal, worklist') := worklist.dequeue? | break
    worklist := worklist'
    -- let some goal ← preprocessGoal goal | continue
    let res ← solve goal
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
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero]) #[m, l, e, monadM, cl])
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
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero]) #[m, l, e, monadM, cl])
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
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero]) #[m, l, e, monadM, cl])
  withLocalDeclD `s nat fun s => do
    let ty ← testBackwardRule ``spec_get_StateT l monadM instWP #[s]
    logInfo m!"Test 3 (get StateM Nat, n=1): {ty}"

/-
@[spec]
theorem Spec.MonadState_get {m ps} [Monad m] [WPMonad m ps] {σ} {Q : PostCond σ (.arg σ ps)} :
    ⦃fun s => Q.fst s s⦄ get (m := StateT σ m) ⦃Q⦄ := by
  simp only [Triple, WP.get_MonadState, WP.get_StateT, SPred.entails.refl]

@[spec]
theorem Spec.MonadState_set {m ps} [Monad m] [WPMonad m ps] {σ} {Q : PostCond σ (.arg σ ps)} :
    ⦃fun s => Q.fst ⟨⟩ s⦄ set s (m := StateT σ m) ⦃Q⦄ := by
  simp only [Triple, WP.set_MonadState, WP.set_StateT, SPred.entails.refl]

def step (v : Nat) : StateM Nat Unit := do
  let s ← get
  set (s + v)
  let s ← get
  set (s - v)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

-- set_option trace.Elab.Tactic.Do.vcgen true in
set_option trace.profiler true in
example : ⦃fun s => ⌜s = 0⌝⦄ loop 50 ⦃⇓_ s => ⌜s = 50⌝⦄ := by
  simp only [loop, step]
  mvcgen'
  -- all_goals grind
  all_goals sorry

set_option trace.Elab.Tactic.Do.vcgen true in
example :
  ⦃⌜True⌝⦄
  do
    let s ← get (m := ExceptT String (StateM Nat))
    if s > 20 then
      throw "s is too large"
    set (m := ExceptT String (StateM Nat)) (s + 1)
  ⦃post⟨fun _r s => ⌜s ≤ 21⌝, fun _err s => ⌜s > 20⌝⟩⦄ := by
  mvcgen' <;> grind
-/

end Test

end Loom
