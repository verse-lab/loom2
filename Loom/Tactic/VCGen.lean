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

def preprocessExpr (e : Expr) : SymM Expr := do
  shareCommon (← unfoldReducible (← instantiateMVars e))

/--
Try to build a backward rule from a single spec theorem in `→` form.

Spec theorems are expected to have conclusion `wp prog post epost s1 ... sn`
(after `forallMetaTelescope` opens all binders including state args and `→` hypotheses).
Unifying `instWP` with the spec's WPMonad instance transitively specializes the lemma
to the concrete monad stack.
-/
def tryMkBackwardRuleFromSpec (specThm : SpecTheorem) (instWP : Expr)
    : OptionT SymM BackwardRule := do
  let (_xs, _bs, specProof, specType) ← specThm.proof.instantiate
  -- specType should be: wp prog post epost s1 ... sn
  specType.withApp fun head args => do
    let_expr wp _m _l _e _monadInst _cl instWP' _α _prog _post _epost :=
      mkAppN head (args.extract 0 (min args.size 10))
      | throwError "target not a wp application {specType}"
    guard <| ← isDefEqGuarded instWP instWP'
  let res ← abstractMVars specProof
  let type ← preprocessExpr (← Sym.inferType res.expr)
  let spec ← Meta.mkAuxLemma res.paramNames.toList type res.expr
  mkBackwardRuleFromDecl spec

/--
Given an array of `SpecTheorem`s (sorted by priority), try to build a backward rule
from the first matching spec. Unifying `instWP` specializes the spec to the goal's monad.
-/
def mkBackwardRuleFromSpecs (specThms : Array SpecTheorem) (instWP : Expr)
    : MetaM (Option (SpecTheorem × BackwardRule)) := SymM.run do
  for specThm in specThms do
    if let some rule ← withNewMCtxDepth
        (tryMkBackwardRuleFromSpec specThm instWP) then
      return (specThm, rule)
  return none

/-! ## VCGen monad and caching -/

structure VCGen.Context where
  specThms : SpecTheorems
  -- TODO: entailsConsIntroRule : BackwardRule

structure VCGen.State where
  /-- Cache mapping spec theorem names × WPMonad instance to their backward rule.
      Avoids rebuilding the same aux lemma repeatedly. -/
  specBackwardRuleCache : Std.HashMap (Array Name × Expr) (SpecTheorem × BackwardRule) := {}
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
    `(spec decl names, instWP)`. -/
def mkBackwardRuleFromSpecsCached (specThms : Array SpecTheorem) (instWP : Expr)
    : OptionT VCGenM (SpecTheorem × BackwardRule) := do
    let decls := specThms.filterMap SpecTheorem.global?
    let cache := (← get).specBackwardRuleCache
    let key := (decls, instWP)
    match cache[key]? with
    | some (specThm, rule) => return (specThm, rule)
    | none =>
      let some rule ← mkBackwardRuleFromSpecs specThms instWP
        | failure
      modify ({ · with specBackwardRuleCache := cache.insert key rule })
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
    let_expr wp _m _l _errTy _monadInst _cl instWP _α e _post _epost :=
      mkAppN head (args.extract 0 (min args.size 10))
      | return .noProgramFoundInTarget target
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
      let some (_, rule) ← (mkBackwardRuleFromSpecsCached thms instWP).run
        | return .noSpecFoundForProgram e instWP thms
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

-- Spec theorems in → form with explicit state arg.
-- Specialized to inner lattice Prop (1 state layer: l = σ → Prop).

@[lspec] theorem spec_get_StateT {m : Type → Type v} {e : Type}
    [Monad m] [LawfulMonad m] [WPMonad m Prop e]
    {σ : Type} (post : σ → σ → Prop) (epost : e) (s : σ) (h : post s s) :
    wp (MonadStateOf.get : StateT σ m σ) post epost s := by
  simp only [WP.get_StateT_wp]; exact h

@[lspec] theorem spec_set_StateT {m : Type → Type v} {e : Type}
    [Monad m] [LawfulMonad m] [WPMonad m Prop e]
    {σ : Type} (x : σ) (post : PUnit → σ → Prop) (epost : e) (s : σ) (h : post ⟨⟩ x) :
    wp (MonadStateOf.set x : StateT σ m PUnit) post epost s := by
  simp only [WP.set_StateT_wp]; exact h

-- Specs for the standalone `get`/`set` functions (which elaborate to MonadState.get/set,
-- a different head constant from MonadStateOf.get/set used above).
@[lspec] theorem spec_get_StateT' {m : Type → Type v} {e : Type}
    [Monad m] [LawfulMonad m] [WPMonad m Prop e]
    {σ : Type} (post : σ → σ → Prop) (epost : e) (s : σ) (h : post s s) :
    wp (get : StateT σ m σ) post epost s :=
  spec_get_StateT post epost s h

@[lspec] theorem spec_set_StateT' {m : Type → Type v} {e : Type}
    [Monad m] [LawfulMonad m] [WPMonad m Prop e]
    {σ : Type} (x : σ) (post : PUnit → σ → Prop) (epost : e) (s : σ) (h : post ⟨⟩ x) :
    wp (set x : StateT σ m PUnit) post epost s :=
  spec_set_StateT x post epost s h

@[lspec] theorem spec_pure {m : Type → Type v} {σ e : Type}
    [Monad m] [WPMonad m (σ → Prop) e]
    {α : Type} (a : α) (post : α → σ → Prop) (epost : e) (s : σ) (h : post a s) :
    wp (pure (f := m) a) post epost s := by
  simp only [WP.pure_wp]; exact h

@[lspec] theorem spec_bind {m : Type → Type v} {σ e : Type}
    [Monad m] [WPMonad m (σ → Prop) e]
    {α β : Type} (x : m α) (f : α → m β) (post : β → σ → Prop) (epost : e) (s : σ)
    (h : wp x (fun a => wp (f a) post epost) epost s) :
    wp (x >>= f) post epost s :=
  WPMonad.wp_bind x f post epost s h

/-- Test helper: create a SpecTheorem from a declaration and run tryMkBackwardRuleFromSpec
    with the given WPMonad instance. Returns the type of the auxiliary lemma. -/
def testBackwardRule (declName : Name) (instWP : Expr) : MetaM Expr := do
  let specThm ← mkSpecTheoremFromConst declName
  let rule ← SymM.run do
    tryMkBackwardRuleFromSpec specThm instWP
  match rule with
  | some br => inferType br.expr
  | none => throwError "tryMkBackwardRuleFromSpec returned none for {declName}"

-- Test 1: spec_bind for StateM Nat — verifies monad specialization
#eval show MetaM Unit from do
  let nat := mkConst ``Nat
  let m ← mkAppM ``StateM #[nat]
  let l ← mkArrow nat (mkSort 0)
  let e := mkConst ``Unit
  let cl ← synthInstance (← mkAppM ``CompleteLattice #[l])
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero]) #[m, l, e, monadM, cl])
  let ty ← testBackwardRule ``spec_bind instWP
  logInfo m!"Test 1 (spec_bind, StateM Nat): {ty}"

-- Test 2: spec_get_StateT for StateM Nat — verifies get spec specialization
#eval show MetaM Unit from do
  let nat := mkConst ``Nat
  let m ← mkAppM ``StateM #[nat]
  let l ← mkArrow nat (mkSort 0)
  let e := mkConst ``Unit
  let cl ← synthInstance (← mkAppM ``CompleteLattice #[l])
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero]) #[m, l, e, monadM, cl])
  let ty ← testBackwardRule ``spec_get_StateT instWP
  logInfo m!"Test 2 (spec_get_StateT, StateM Nat): {ty}"

def step (v : Nat) : StateM Nat Unit := do
  let s ← get
  set (s + v)
  let s ← get
  set (s - v)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ s post (h : post s), wp (loop n) (fun _ => post) () s

def driver (n : Nat) (check := true) (k : MVarId → MetaM Unit) : MetaM Unit := do
  let some goal ← unfoldDefinition? (mkApp (mkConst ``Goal) (mkNatLit n)) | throwError "UNFOLD FAILED!"
  let mvar ← mkFreshExprMVar goal
  let startTime ← IO.monoNanosNow
  k mvar.mvarId!
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  if check then
    let startTime ← IO.monoNanosNow
    checkWithKernel (← instantiateExprMVars mvar)
    let endTime ← IO.monoNanosNow
    let kernelMs := (endTime - startTime).toFloat / 1000000.0
    IO.println s!"goal_{n}: {ms} ms, kernel: {kernelMs} ms"
  else
    IO.println s!"goal_{n}: {ms} ms"

macro "solve" : tactic => `(tactic| {
  intro s post h
  simp only [loop, step]
  mvcgen' <;> grind
})

def solveUsingMeta (n : Nat) (check := true) : MetaM Unit := do
  driver n check fun mvarId => do
    let ([], _) ← Lean.Elab.runTactic mvarId (← `(tactic| solve)).raw {} {} | throwError "FAILED!"

def runBenchUsingMeta (sizes : List Nat) : MetaM Unit := do
  IO.println "=== VCGen tests ==="
  IO.println ""
  for n in sizes do
    solveUsingMeta n


set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

#eval runBenchUsingMeta [400]

-- -- set_option trace.profiler true in
-- example (p : Nat -> Prop) : Triple p (loop 1000) (fun _ => p) () := by
--   simp only [Triple.iff, loop, step,]
--   intro s hs
--   mvcgen'
--   all_goals sorry

end Test

end Loom
