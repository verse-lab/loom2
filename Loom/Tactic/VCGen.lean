/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
import Lean
import Loom.Tactic.Attr
import Loom.Tactic.Spec
import Loom.Tactic.Logic
import Loom.Triple.Basic
import Loom.Triple.SpecLemmas
import Loom.WP.Lemmas
import Loom.Frame
import Loom.Tactic.ShareExt
import Loom.Tactic.Match
import Loom.Tactic.VCGenTime

open Lean Parser Meta Elab Tactic Sym Loom Lean.Order
open Loom.Tactic.SpecAttr
open Std.Do'
open Grind (GrindM)

namespace Loom

initialize registerTraceClass `Loom.Tactic.vcgen

inductive VCGen.dischargeTactic where
  | none
  | grind
  | tactic (tactic : Syntax)
  deriving Repr

def VCGen.dischargeTactic.isGrind : VCGen.dischargeTactic → Bool
  | .grind => true
  | _      => false

def VCGen.dischargeTactic.eval (goal : MVarId) : VCGen.dischargeTactic → MetaM (List MVarId)
  | .none => return [goal]
  | .grind => unreachable!
  | .tactic tac => do
    let (goals, _) ← runTactic goal tac
    return goals

/-! ## VCGen monad and caching -/

structure VCGen.Context where
  specThms     : SpecTheorems
  introPreRule : BackwardRule
  elimPreRule  : BackwardRule
  disch        : dischargeTactic := .none

structure VCGen.State where
  specBackwardRuleCache  : Std.HashMap (Name × Expr × Nat) BackwardRule := {}
  splitBackwardRuleCache : Std.HashMap (Name × Expr × Nat) BackwardRule := {}
  logicBackwardRuleCache : Std.HashMap (Name × Array Expr × Nat) BackwardRule := {}
  invariants             : Array MVarId := #[]
  vcs                    : Array MVarId := #[]

abbrev VCGenM := ReaderT VCGen.Context (StateRefT VCGen.State GrindM)

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


open Lean.Elab.Tactic.Do in
def mkBackwardRuleForSplitCached
    (splitInfo : SplitInfo) (wpHead m l errTy monadInst instWP : Expr)
    (excessArgs : Array Expr) : VCGenM BackwardRule := do
  let cacheKey := match splitInfo with
    | .ite .. => ``ite
    | .dite .. => ``dite
    | .matcher matcherApp => matcherApp.matcherName
  let s := (← get).splitBackwardRuleCache
  match s[(cacheKey, instWP, excessArgs.size)]? with
  | some rule => return rule
  | none =>
    let rule ← mkBackwardRuleForSplit splitInfo wpHead m l errTy monadInst instWP excessArgs
    modify ({ · with splitBackwardRuleCache := s.insert (cacheKey, instWP, excessArgs.size) rule })
    return rule

def mkBackwardRuleForLogicCached
    (lop : LogicOp) (as excessArgs : Array Expr) : VCGenM BackwardRule := do
  let s := (← get).logicBackwardRuleCache
  let asTypes ← (as.mapM Sym.inferType : SymM (Array Expr))
  let key := (lop.toApplyLemma, asTypes, excessArgs.size)
  match s[key]? with
  | some rule => return rule
  | none =>
    let rule ← LogicOp.mkBackwardRule lop as excessArgs
    modify ({ · with logicBackwardRuleCache := s.insert key rule })
    return rule

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
  | EPostVC (relConst : Expr) (α inst : Expr) (pre : Expr) (epost : Expr) (excessArgs : Array Expr)
  /-- RHS is a lattice connective application (`meet`/`himp`) with optional excess args. -/
  | Lattice (lop : LogicOp) (as : Array Expr) (excessArgs : Array Expr)
  /-- RHS is a WP application. -/
  | WP (head : Expr) (args : Array Expr)
  /-- Lattice type is Prop and precondition is not `True`; intro the pre. -/
  | IntroPre
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
  match_expr target with
  | PartialOrder.rel α inst pre rhs =>

    if !pre.isConstOf ``True && α.isProp then return .IntroPre

    rhs.withApp fun head args => do
      match_expr head with
      | EPost.cons.head =>
        let some epostArg := args[2]?
          | return .Unknown
        let (epostTarget, index) := peelEPostTailChain epostArg
        let epost ← mkEPostAtIndex epostTarget index
        return .EPostVC target.getAppFn α inst pre epost (args.extract 3 args.size)
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
    -- else return .IntroPre
  | _ => return .Unknown

/-- Main solve step for a goal of the form `pre ⊑ rhs`. -/
def solve (goal : MVarId) : VCGenM SolveResult := goal.withContext do
  let target ← goal.getType
  let kind ← classifyGoalKind target
  match kind with
  | .TrivialTrue => do
      throwError "TrivialTrue not yet implemented in VCGen'"
  | .IntroPre => do
      let rule := (← read).introPreRule
      let .goals goals ← rule.apply goal
        | throwError "Failed to apply intro_pre rule"
      let goals ← goals.mapM fun g => do
        let .goal _ g ← Sym.intros g | throwError "Failed to intro pre"
        return g
      return .goals goals
  | .Unknown =>
      return .noProgramOrLatticeFoundInTarget target
  | .Lattice lop as excessArgs => do
      trace[Loom.Tactic.vcgen] "Applying logic rule for {target}. Excess args: {excessArgs}"
      let rule ← mkBackwardRuleForLogicCached lop as excessArgs
      let .goals goals ← rule.apply goal
        | throwError "Failed to apply logic rule at {indentExpr target}"
      return .goals goals
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
      -- Split ite/dite/match
      if let some info ← liftMetaM <| Lean.Elab.Tactic.Do.getSplitInfo? e then
        -- For matchers, try reduceRecMatcher? to reduce known discriminants
        if let .matcher .. := info then
          if let some e' ← liftMetaM <| Lean.Meta.reduceRecMatcher? e then
            trace[Loom.Tactic.vcgen] "reduceRecMatcher simplified match in {e}"
            let e' ← shareCommon e'
            let rhs ← mkAppNS head <| args.set! 6 e'
            let relArgs := target.getAppArgs
            let newTarget ← mkAppNS target.getAppFn (relArgs.set! (relArgs.size - 1) rhs)
            let goal ← goal.replaceTargetDefEq newTarget
            return .goals [goal]
        -- Fall back to full split
        trace[Loom.Tactic.vcgen] "Applying split rule for {e}. Excess args: {excessArgs}"
        let rule ← mkBackwardRuleForSplitCached info head m l errTy monadInst instWP excessArgs
        let .goals goals ← rule.apply goal
          | throwError "Failed to apply split rule for {indentExpr e}"
        let goals ← goals.mapM fun g => do
          let .goal _ g ← Sym.intros g
            | throwError "Failed to intro split parameters"
          return g
        return .goals goals
      -- Apply registered specifications
      let f := e.getAppFn
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
  | .EPostVC relConst α inst pre epost excessArgs => do
      let rhs ← betaRevS epost excessArgs.reverse
      let newTarget ← mkAppNS relConst #[α, inst, pre, rhs]
      let goal ← goal.replaceTargetDefEq newTarget
      return .goals [goal]

/-- Emit a VC for a goal that cannot be further decomposed.
    If the goal is `True ⊑ x` (on Prop), first eliminate the `True ⊑` wrapper. -/
meta def emitVC (goal : Grind.Goal) : VCGenM Unit := do
  let mut goal := goal
  let ty ← goal.mvarId.getType
  if let some (_, _, Expr.const ``True _, _) := ty.app4? ``PartialOrder.rel then
    let rule := (← read).elimPreRule
    let .goals [goal'] ← goal.apply rule
      | throwError "Failed to apply elim_pre rule"
    goal := goal'
  let disch := (← read).disch
  let mut goals := [goal.mvarId]
  match disch with
  | .grind =>
    match ← goal.timedTryGrind with
    | none => goals := []
    | some sub => goals := [sub]
  | _ => goals ← disch.eval goal.mvarId
  for g in goals do g.setKind .syntheticOpaque
  modify fun s => { s with vcs := s.vcs ++ goals }

/-- Unfold `⦃P⦄ x ⦃Q⦄` into `P ⊑ wp⟦x⟧ Q`. -/
meta def unfoldTriple (goal : Grind.Goal) : OptionT VCGenM Grind.Goal := goal.withContext do
  let type ← goal.mvarId.getType
  unless type.isAppOf ``Triple do return goal
  let rule ← mkBackwardRuleFromDecl ``Triple.intro
  let .goals [goal] ← goal.apply rule | failure
  return goal

def introsWP (goal : Grind.Goal) : VCGenM Grind.Goal := do
  let mut goal := goal
  if (← goal.mvarId.getType).isForall then
    let .goal _ goal' ← goal.intros #[] | failure
    goal := goal'
  return goal

/-- Main work loop: decompose the goal repeatedly. -/
meta def work (goal : MVarId) : VCGenM Unit := do
  let goal ← Grind.mkGoal goal
  let some goal ← unfoldTriple goal |>.run | return ()
  let mut worklist := Std.Queue.empty.enqueue goal
  repeat do
    let some (goal, worklist') := worklist.dequeue? | break
    worklist := worklist'
    let goal ← introsWP goal
    let res ← solve goal.mvarId
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
      -- if we have multiple subgoals, before running the VCGen
      -- we need to share the grind context first.
      -- TODO: I am afraid of excessive copying of the grind context.
      let mut grindSharedGoal := goal
      if (← read).disch.isGrind && subgoals.length > 1 then
        grindSharedGoal ← goal.timedInternalizeAll
      worklist := worklist.enqueueAll <| subgoals.map ({ grindSharedGoal with mvarId := · })

public structure Result where
  invariants : Array MVarId
  vcs : Array MVarId

/-- Generate VCs for a goal of the form `Triple pre e post epost`, keeping subgoals in `⊑` form. -/
public meta partial def main (goal : MVarId) (ctx : Context) : GrindM Result := do
  let doTime := vcgen.time.get (← getOptions)
  if doTime then vcgenTimingRef.set {}
  let ((), state) ← StateRefT'.run (ReaderT.run (work goal) ctx) {}
  for h : idx in [:state.invariants.size] do
    let mv := state.invariants[idx]
    mv.setTag (Name.mkSimple ("inv" ++ toString (idx + 1)))
  for h : idx in [:state.vcs.size] do
    let mv := state.vcs[idx]
    mv.setTag (Name.mkSimple ("vc" ++ toString (idx + 1)) ++ (← mv.getTag).eraseMacroScopes)
  return { invariants := state.invariants, vcs := state.vcs }

syntax (name := mvcgen') "mvcgen'"
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) " ] ")?
  (&" with " tactic)?  : tactic

def VCGen.getDischargeTactic (stx : Syntax) : MetaM VCGen.dischargeTactic := do
  let .some tac := stx[2][1]? | return .none
  if tac.isMissing then return .none
  return if tac.getKind == ``Parser.Tactic.grind then
      .grind
    else
    .tactic tac

@[tactic mvcgen']
public meta def VCGen.elab : Tactic := fun stx => withMainContext do
  let ctx ← getSpecTheorems
  let goal ← getMainGoal

  let withClause := stx[2]
  let hasWithClause := withClause.getNumArgs != 0
  let mut disch ← getDischargeTactic stx
  let mut params ← Grind.mkDefaultParams {}

  if let .grind := disch then
    let grindStx := withClause[1]
    let `(tactic| grind $config:optConfig $[only%$only]? $[ [$grindParams:grindParam,*] ]? $[=> $_:grindSeq]?) := grindStx
      | throwUnsupportedSyntax
    let grindConfig ← elabGrindConfig config
    params ← mkGrindParams grindConfig only.isSome (grindParams.getD {}).getElems goal
    -- FIXME: Expose grind's internal simp step limit as a user-facing option instead of hardcoding.
    -- Grind's `simpCore` uses the default `Simp.Config.maxSteps` (100k) which is too low for large
    -- unrolled goals (fails around n=400 for GetThrowSet).
    params := { params with norm := ← params.norm.setConfig { params.norm.config with maxSteps := 10000000 } }

  -- dbg_trace "disch: {repr disch}"
  let { invariants, vcs } ← Grind.GrindM.run (params := params) do
    let migratedCtx ← migrateSpecTheoremsDatabase ctx
    let introPreRule ← mkBackwardRuleFromDecl ``prop_pre_intro
    let elimPreRule ← mkBackwardRuleFromDecl ``prop_pre_elim
    VCGen.main goal { specThms := migratedCtx, introPreRule, elimPreRule, disch }
  replaceMainGoal (invariants ++ vcs).toList

end VCGen

end Loom
