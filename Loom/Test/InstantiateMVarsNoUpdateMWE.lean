import Lean
import Lean.Meta.InstMVarsNU

open Lean Meta
open Lean.Meta.Sym

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

/-
This is a smaller Lean-only reduction of the `AssertGadgetStep` slowdown.
It keeps only the operations that matter for the regression:

* `Sym.preprocessMVar`
* repeated `Sym.intros`
* repeated `BackwardRule.apply` with `And.intro`
* timing `instantiateMVarsNoUpdate` on the original root metavariable
-/

private def timeItMs (k : MetaM α) : MetaM (α × UInt64) := do
  let startTime ← IO.monoNanosNow
  let a ← k
  let endTime ← IO.monoNanosNow
  let ms := (endTime - startTime).toFloat / 1000000.0
  return (a, ms.toUInt64)

/--
`mkGoalType n` builds

`∀ s, ((s = s -> ((s+1) = (s+1) -> ... True) ∧ ((s+1) = (s+1))) ∧ (s = s))`

This preserves the shape that matters for the slowdown without depending on any
user-level program logic.
-/
private def mkGoalType (n : Nat) : MetaM Expr := do
  let nat := mkConst ``Nat
  withLocalDeclD `s nat fun s => do
    let rec go (s : Expr) : Nat → MetaM Expr
      | 0 => pure (mkConst ``True)
      | n + 1 => do
        let succS := mkApp (mkConst ``Nat.succ) s
        let ih ← go succS n
        let eq ← mkEq s s
        let imp ← mkArrow eq ih
        pure (mkApp2 (mkConst ``And) imp eq)
    mkForallFVars #[s] (← go s n)

run_meta do
  for n in [1, 2, 3, 4] do
    let goalTy ← mkGoalType n
    logInfo m!"mkGoalType {n}:{indentExpr goalTy}"

elab "solveGoal" : tactic => do Elab.Tactic.evalTactic $
  <- `(tactic|(
    repeat'
      first
        | (intro)
        | (apply And.intro)
        | (exact True.intro)
        | rfl
    ))

private def dischargeLeaf (mvarId : MVarId) : MetaM Unit := do
  mvarId.withContext do
    let target ← instantiateMVars (← mvarId.getType)
    if target.isTrue then
      mvarId.assign (mkConst ``True.intro)
      return ()
    match target.eq? with
    | some (_, lhs, rhs) =>
      unless lhs == rhs do
        throwError "unsupported non-reflexive VC:{indentExpr target}"
      mvarId.assign (← mkEqRefl lhs)
    | none =>
      throwError "unsupported VC:{indentExpr target}"

/--
Construct the solved root metavariable in the same shape as `Driver`:
the root goal is created first, then assigned by symbolic proof search, and only
afterwards do we time `instantiateMVarsNoUpdate root`.
-/
private def mkSolvedRoot (n : Nat) : MetaM (Expr × UInt64) := do
  let root ← mkFreshExprMVar (← mkGoalType n)
  let (_, solveMs) ← timeItMs do
    Lean.Elab.runTactic root.mvarId! (← `(tactic| solveGoal)).raw {} {}
  return (root, solveMs)

private def timeMethod
    (n : Nat) (k : Expr → MetaM Expr) : MetaM (UInt64 × UInt64 × UInt64) := do
  let saved ← saveState
  try
    let (root, solveMs) ← mkSolvedRoot n
    let (expr, instMs) ← timeItMs (k root)
    let (_, shareMs) ← timeItMs do
      let _ ← SymM.run (shareCommon expr)
      pure ()
    return (instMs, shareMs, solveMs)
  finally
    saved.restore

private def benchOne (n : Nat) : MetaM Unit := do
  let (instMs, instShareMs, solveMs) ← timeMethod n instantiateMVars
  let (noUpdateMs, noUpdateShareMs, _) ← timeMethod n instantiateMVarsNoUpdate
  let (noUpdateLeanMs, noUpdateLeanShareMs, _) ← timeMethod n instantiateMVarsNoUpdateLean
  IO.println s!"goal_{n}: solve={solveMs} ms, instantiate={instMs}+{instShareMs} ms, noUpdate={noUpdateMs}+{noUpdateShareMs} ms, noUpdateLean={noUpdateLeanMs}+{noUpdateLeanShareMs} ms"

run_meta do
  for n in [200] do
    benchOne n
