import Lean
import Loom.Tactic.Attr
import Loom.Tactic.Spec
import Loom.Tactic.Logic
import Loom.Triple.Basic
import Loom.Triple.SpecLemmas
import Loom.WP.SimpLemmas
import Loom.Frame
import Lean.Meta
import Lean.Meta.Match.Rewrite
import Loom.Tactic.ShareExt

open Lean Parser Meta Elab Tactic Sym Loom Lean.Order
open Loom.Tactic.SpecAttr
open Loom.Tactic.Spec

namespace Loom

initialize registerTraceClass `Loom.Tactic.vcgen

/-! ## VCGen monad and caching -/

structure VCGen.Context where
  specThms : SpecTheorems

structure VCGen.State where
  specBackwardRuleCache : Std.HashMap (Name × Expr × Nat) BackwardRule := {}
  splitBackwardRuleCache : Std.HashMap (Name × Expr × Nat) BackwardRule := {}
  logicBackwardRuleCache : Std.HashMap (Name × Array Expr × Nat) BackwardRule := {}
  invariants : Array MVarId := #[]
  vcs : Array MVarId := #[]

abbrev VCGenM := ReaderT VCGen.Context (StateRefT VCGen.State SymM)

namespace VCGen

/-! ## Backward rule construction -/

/-- Cached version of `tryMkBackwardRuleFromSpec`.
    Cache key: `(proof key, instWP, excessArgs.size)`. -/
def mkBackwardRuleFromSpecCached (specThm : SpecTheorem)
    (l instWP : Expr) (excessArgs : Array Expr)
    : OptionT VCGenM BackwardRule := do
    let key := (specThm.proof.key, instWP, excessArgs.size)
    let s := (← get).specBackwardRuleCache
    match s[key]? with
    | some rule => return rule
    | none =>
      let some rule ← (withNewMCtxDepth
          (tryMkBackwardRuleFromSpec specThm l instWP excessArgs).run : SymM _)
        | failure
      modify fun st => { st with specBackwardRuleCache := st.specBackwardRuleCache.insert key rule }
      return rule

def mkBackwardRuleForIteCached
    (_wpHead _m _l _errTy _monadInst _instWP : Expr)
    (_excessArgs : Array Expr) : VCGenM BackwardRule := do
  throwError "mkBackwardRuleForIteCached not yet implemented in VCGen'"

def mkBackwardRuleForLogicCached
    (_lop : LogicOp) (_as _excessArgs : Array Expr) : VCGenM BackwardRule := do
  throwError "mkBackwardRuleForLogicCached not yet implemented in VCGen'"

/-! ## Goal classification -/

/-- Result of trying to solve a single goal of the form `pre ⊑ wp prog post epost`. -/
inductive SolveResult where
  /-- The RHS was neither a WP goal nor a supported lattice goal. -/
  | noProgramOrLatticeFoundInTarget (T : Expr)
  /-- Don't know how to handle `e` in `pre ⊑ wp e post epost`. -/
  | noStrategyForProgram (e : Expr)
  /-- Did not find a spec for `e` in `pre ⊑ wp e post epost`. -/
  | noSpecFoundForProgram (e : Expr) (monad : Expr) (thms : Array SpecTheorem)
  /-- Successfully decomposed the goal. These are the subgoals. -/
  | goals (subgoals : List MVarId)

/-- High-level classifier for the RHS of a `pre ⊑ rhs` goal. -/
inductive GoalKind where
  /-- RHS is `True`; dischargeable via `le_top` or similar. -/
  | TrivialTrue
  /-- RHS is a concrete EPost component; stores selected component and its excess args. -/
  | EPostVC (epost : Expr) (excessArgs : Array Expr)
  /-- RHS is a lattice connective application (`meet`/`himp`) with optional excess args. -/
  | Lattice (lop : LogicOp) (as : Array Expr) (excessArgs : Array Expr)
  /-- RHS is a WP application. -/
  | WP (head : Expr) (args : Array Expr)
  /-- RHS is neither a recognized WP nor a recognized lattice connective. -/
  | Unknown

/-! ## Private helpers -/

/-- Get the `index`-th component from an `EPost` target. -/
private def mkEPostAtIndex (target : Expr) (index : Nat) : SymM Expr := do
  let mut curr := target
  for _ in [:index] do
    let_expr EPost.cons.mk _ _ _ tail := curr
      | throwError "Expected EPost.cons.mk, got {curr}"
    curr := tail
  let_expr EPost.cons.mk _ _ head _ := curr
    | throwError "Expected EPost.cons.mk, got {curr}"
  return head

/-- Peel a chain of `.tail` projections, returning the base `EPost` and the number of tails. -/
private partial def peelEPostTailChain (curr : Expr) (idx : Nat := 0) : Expr × Nat :=
  curr.consumeMData.withApp fun fn args =>
    if fn.isConstOf ``EPost.cons.tail && args.size > 0 then
      peelEPostTailChain args[args.size - 1]! (idx + 1)
    else
      (curr, idx)

/-! ## Core logic -/

/-- Classify the RHS of a `pre ⊑ rhs` goal. If the target is not in `⊑` form,
    falls back to classifying the target directly. -/
def classifyGoalKind (target : Expr) : VCGenM GoalKind := do
  -- Try to decompose as PartialOrder.rel _ _ pre rhs
  let rhs :=
    match_expr target with
    | PartialOrder.rel _ _ _pre rhs => rhs
    | _ => target
  rhs.withApp fun head args => do
    match_expr head with
    | True => return .TrivialTrue
    | EPost.cons.head =>
        let some epostArg := args[2]?
          | return .Unknown
        let (epostTarget, index) := peelEPostTailChain epostArg
        let epost ← mkEPostAtIndex epostTarget index
        return .EPostVC epost (args.extract 3 args.size)
    | wp => return .WP head args
    | meet =>
      let excessArgs := args.drop 4
      let as := args.extract 2 4
      return .Lattice .And as excessArgs
    | himp =>
      let excessArgs := args.drop 4
      let as := args.extract 2 4
      return .Lattice .Imp as excessArgs
    | _ => return .Unknown

/-- Main solve step for a goal of the form `pre ⊑ rhs`. -/
def solve (goal : MVarId) : VCGenM SolveResult := goal.withContext do
  let target ← goal.getType
  let kind ← classifyGoalKind target
  match kind with
  | .TrivialTrue => do
      throwError "TrivialTrue not yet implemented in VCGen'"
  | .Unknown =>
      return .noProgramOrLatticeFoundInTarget target
  | .Lattice _lop _as _excessArgs => do
      throwError "Lattice not yet implemented in VCGen'"
  | .WP head args => do
      -- Goal is: pre ⊑ @wp m l errTy monadInst instWP α e post epost
      let_expr wp m l errTy monadInst instWP α e _post _epost :=
        mkAppN head <| args.take 9
        | return .noProgramOrLatticeFoundInTarget target
      let excessArgs := args.extract 9 args.size
      -- Non-dependent let-expressions
      let f := e.getAppFn
      if let .letE _x _ty val body _nonDep := f then
        let body' ← Sym.instantiateRevBetaS body #[val]
        let e' ← mkAppRevS body' e.getAppRevArgs
        let wp ← mkAppS₉ head m l errTy monadInst instWP α e' _post _epost
        let rhs ← mkAppNS wp excessArgs
        -- Rebuild the ⊑ goal with the new RHS
        let_expr PartialOrder.rel l cl pre _rhs := target
          | throwError "expected ⊑ goal but got {target}"
        let newTarget ← mkAppNS (mkConst ``PartialOrder.rel) #[l, cl, pre, rhs]
        let goal ← goal.replaceTargetDefEq newTarget
        return .goals [goal]
      -- Apply registered specifications
      let f := e.getAppFn
      if f.isConstOf ``ite || f.isAppOf ``ite then
        let rule ← mkBackwardRuleForIteCached head m l errTy monadInst instWP excessArgs
        trace[Loom.Tactic.vcgen] "Applying split rule for {e}. Excess args: {excessArgs}"
        let .goals goals ← rule.apply goal
          | throwError "Failed to apply split rule for {indentExpr e}"
        return .goals goals
      if f.isConst || f.isFVar then
        trace[Loom.Tactic.vcgen] "Applying a spec for {e}. Excess args: {excessArgs}"
        match ← findSpecs (← read).specThms e with
        | .error thms => return .noSpecFoundForProgram e m thms
        | .ok thm =>
        trace[Loom.Tactic.vcgen] "Spec for {e}: {thm.proof}"
        let some rule ← (mkBackwardRuleFromSpecCached thm l instWP excessArgs).run
          | return .noSpecFoundForProgram e m #[thm]
        trace[Loom.Tactic.vcgen] "Applying rule {rule.pattern.pattern} at {target}"
        let .goals goals ← rule.apply goal
          | throwError "Failed to apply rule {thm.proof} for {indentExpr e}"
        return .goals goals
      return .noStrategyForProgram e
  | .EPostVC _epost _excessArgs => do
      throwError "EPostVC not yet implemented in VCGen'"

/-- Emit a VC for a goal that cannot be further decomposed. -/
meta def emitVC (goal : MVarId) : VCGenM Unit := do
  let ty ← goal.getType
  goal.setKind .syntheticOpaque
  if ty.isAppOf ``Std.Do.Invariant then
    modify fun s => { s with invariants := s.invariants.push goal }
  else
    modify fun s => { s with vcs := s.vcs.push goal }

/-- Unfold `⦃P⦄ x ⦃Q⦄` into `P ⊑ wp⟦x⟧ Q`. -/
meta def unfoldTriple (goal : MVarId) : OptionT SymM MVarId := goal.withContext do
  let type ← goal.getType
  unless type.isAppOf ``Triple do return goal
  let simpTripleMethod ← mkMethods #[``Triple.iff]
  let (res, _) ← Simp.SimpM.run (simpGoal (methods := simpTripleMethod) goal)
  match res with
  | .goal goal => return goal
  | .closed => failure
  | .noProgress => return goal

/-- Main work loop: decompose the goal repeatedly. -/
meta def work (goal : MVarId) : VCGenM Unit := do
  let goal ← preprocessMVar goal
  let some goal ← unfoldTriple goal |>.run | return ()
  -- No introsWP — we keep goals in ⊑ form
  let mut worklist := Std.Queue.empty.enqueue goal
  repeat do
    let some (goal, worklist') := worklist.dequeue? | break
    worklist := worklist'
    let res ← solve goal
    match res with
    | .noProgramOrLatticeFoundInTarget .. =>
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

/-- Generate VCs for a goal of the form `Triple pre e post epost`, keeping subgoals in `⊑` form. -/
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
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) " ] ")? : tactic

@[tactic mvcgen']
public meta def elabMVCGen' : Tactic := fun _stx => withMainContext do
  let ctx ← getSpecTheorems
  let goal ← getMainGoal
  let { invariants, vcs } ← SymM.run do
    let migratedCtx ← migrateSpecTheoremsDatabase ctx
    VCGen.main goal { specThms := migratedCtx }
  replaceMainGoal (invariants ++ vcs).toList

end VCGen

end Loom
