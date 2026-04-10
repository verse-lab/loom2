import Lean

open Lean Meta Elab Tactic Sym

/-- Conclusion `∃ n, P n` is `Exists (fun n => P n)` — the lambda triggers
    deferred higher-order matching for pattern variable `P`. -/
theorem ho_rule (P : Nat → Prop) (h : P 42) : ∃ n, P n := ⟨42, h⟩

elab "demo_backward_rule_mvars" : tactic => do
  let goal ← getMainGoal
  let rule ← mkBackwardRuleFromDecl ``ho_rule
  logInfo m!"resultPos: {rule.resultPos}, numVars: {rule.pattern.varTypes.size}"
  let .goals subgoals ← SymM.run (rule.apply goal)
    | throwError "rule not applicable"
  for g in subgoals do
    let ty ← g.getType
    let mvars := (ty.collectMVars {}).result
    logInfo m!"hasExprMVar = {ty.hasExprMVar}, #mvars = {mvars.size}, type: {ty}"
    for mv in mvars do
      if ← mv.isAssigned then
        let val ← instantiateMVars (.mvar mv)
        logInfo m!"  {mv.name} assigned → {val}"
  replaceMainGoal subgoals

example : ∃ n, n > 0 := by
  demo_backward_rule_mvars
  · omega