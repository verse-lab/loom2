import Lean
open Lean Meta Elab Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 100000000

def Goal (k : Nat) : Nat → Prop
  | 0 => True
  | n+1 => ∀ (m : Nat), k = m.succ → Goal m n

open Sym Grind in
elab "internalizeAll" : tactic => do
  let goal ← getMainGoal
  let params ← Grind.mkDefaultParams {}
  GrindM.run (params := params) do
    let goal ← Grind.mkGoal goal
    let t ← IO.monoNanosNow
    let goal ← goal.internalizeAll
    let t' ← IO.monoNanosNow
    dbg_trace s!"internalize={(t' - t) / 1000000}ms"
    match ← goal.grind with
    | .closed => return ()
    | .failed _ => throwError "grind failed"

example : let steps := 140; Goal n steps := by
  simp only [Goal]; intros
  internalizeAll
