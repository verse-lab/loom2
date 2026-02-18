import Lean
import Loom.Tactic.Attr
import Loom.Triple.Basic
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
  (l monadInst _instWP : Expr) (excessArgs : Array Expr) : OptionT SymM BackwardRule := do
  -- Instantiate the spec theorem, creating metavars for all universally quantified params
  let (_xs, _bs, specProof, specType) ← specThm.proof.instantiate
  let_expr PartialOrder.rel l' _cl' pre rhs := specType
    | throwError "target not a partial order ⊑ application {specType}"
  guard <| ← isDefEqS l l' -- Ensure the spec's lattice type matches the goal's (e.g. both `Nat → Prop`)
  let_expr wp _m' _ _e' _monadInst' _cl' _instWP' _α _prog _post _epost := rhs
    | throwError "target not a wp application {rhs}"
  guard <| ← isDefEqS monadInst _monadInst'
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
@[lspec] theorem spec_get_StateT {m : Type u → Type v} {l : Type u} {es : List (Type u)}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l es]
    {σ : Type u} (post : σ → σ → l) (epost : EPost es) :
    (fun s => post s s) ⊑ wp (MonadStateOf.get : StateT σ m σ) post epost := by
  exact WP.get_StateT_wp post epost

@[lspec] theorem spec_set_StateT {m : Type u → Type v} {l : Type u} {es : List (Type u)}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l es]
    {σ : Type u} (x : σ) (post : PUnit → σ → l) (epost : EPost es) :
    (fun _ => post ⟨⟩ x) ⊑ wp (MonadStateOf.set x : StateT σ m PUnit) post epost := by
  exact WP.set_StateT_wp x post epost

-- Specs for the standalone `get`/`set` functions (which elaborate to MonadState.get/set,
-- a different head constant from MonadStateOf.get/set used above).
@[lspec] theorem spec_get_StateT' {m : Type u → Type v} {l : Type u} {es : List (Type u)}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l es]
    {σ : Type u} (post : σ → σ → l) (epost : EPost es) :
    (fun s => post s s) ⊑ wp (get : StateT σ m σ) post epost :=
  spec_get_StateT post epost

@[lspec] theorem spec_set_StateT' {m : Type u → Type v} {l : Type u} {es : List (Type u)}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l es]
    {σ : Type u} (x : σ) (post : PUnit → σ → l) (epost : EPost es) :
    (fun _ => post ⟨⟩ x) ⊑ wp (set x : StateT σ m PUnit) post epost :=
  spec_set_StateT x post epost

@[lspec] theorem spec_pure {m : Type u → Type v} {l : Type u} {es : List (Type u)}
    [Monad m] [CompleteLattice l] [WPMonad m l es]
    {α : Type u} (a : α) (post : α → l) (epost : EPost es) :
    post a ⊑ wp (pure (f := m) a) post epost := by
  exact WPMonad.wp_pure a post epost

@[lspec] theorem spec_bind {m : Type u → Type v} {l : Type u} {es : List (Type u)}
    [Monad m] [CompleteLattice l] [WPMonad m l es]
    {α β : Type u} (x : m α) (f : α → m β) (post : β → l) (epost : EPost es) :
    wp x (fun a => wp (f a) post epost) epost ⊑ wp (x >>= f) post epost :=
  WPMonad.wp_bind x f post epost

end Test

end Loom
