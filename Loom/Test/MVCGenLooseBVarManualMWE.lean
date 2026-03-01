import Lean
import Loom.Test.Specs
import Loom.Tactic.VCGen

open Loom Lean Meta Elab Tactic Order
open Lean.Meta.Sym
open Loom.Tactic.SpecAttr

/-
Manual minimal repro for the current loose-bvar regression, specialized to

  wp (do let x <- get; set x) (fun _ s' => s = s') ⟨⟩ s

Unlike `mvcgen'`, this tactic does not use `mkBackwardRuleFromSpecs`.
Instead, it applies two hand-written specialized rules directly with
`BackwardRule.apply`.

After the second step, the produced subgoal is malformed:

  wp (set #0) (fun x s' => s = s') epost⟨⟩ s

The final `findSpecs` call on that malformed program reproduces the same
`unknown goal` / `loose bvar in expression` failure.
-/

abbrev Post := PUnit → Nat → Prop
abbrev GetPost := Nat → Nat → Prop

theorem bind_get_set_rule (s : Nat) (post : Post) :
    wp (get (m := StateM Nat)) (fun a => wp (set (m := StateM Nat) a) post epost⟨⟩) epost⟨⟩ s →
    wp (do
      let x <- get (m := StateM Nat)
      set (m := StateM Nat) x)
      post
      epost⟨⟩
      s := by
  sorry

theorem get_state_rule (s : Nat) (post : GetPost) :
    (fun s' => post s' s') s →
    wp (get (m := StateM Nat)) post epost⟨⟩ s := by
  sorry

private def applyRuleNamed (goal : MVarId) (ruleName : Name) : MetaM (List MVarId) := goal.withContext do
  let rule ← mkBackwardRuleFromDecl ruleName
  let res ← SymM.run <| BackwardRule.apply goal rule
  match res with
  | .goals goals => pure goals
  | .failed => throwError "failed to apply {ruleName}"

private def parseWpProg (goal : MVarId) : MetaM Expr := goal.withContext do
  let target ← goal.getType
  let head := target.getAppFn
  let args := target.getAppArgs
  let_expr wp _m _l _errTy _monadInst _instWP _α e _post _epost :=
    mkAppN head (args.extract 0 (min args.size 9))
    | throwError "expected a WP goal, got {indentExpr target}"
  pure e

elab "manualGetSetBug" : tactic => withMainContext do
  let goal ← getMainGoal
  let goal ← SymM.run <| preprocessMVar goal

  let [goal] ← applyRuleNamed goal ``bind_get_set_rule
    | throwError "expected one subgoal after bind_get_set_rule"
  let [goal] ← applyRuleNamed goal ``get_state_rule
    | throwError "expected one subgoal after get_state_rule"

  logInfo m!"Malformed intermediate goal: {← goal.getType}"

  let e ← parseWpProg goal
  let db ← getSpecTheorems
  let _ ← db.findSpecs e

  replaceMainGoal [goal]

example (s : Nat) :
    wp (do
      let x <- get (m := StateM Nat)
      set (m := StateM Nat) x)
      (fun _ s' => s = s')
      epost⟨⟩
      s := by
  manualGetSetBug
