import Lean
import Loom.Tactic.VCGen

open Loom Lean Meta Order

def step (v : Nat) : StateM Nat Unit := do
  let s ← get
  set (s + v)
  let s ← get
  set (s - v)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ s post (_ : post s), wp (loop n) (fun _ => post) EPost.nil.mk s

def driver (n : Nat) (check := true) (k : MVarId → MetaM (List MVarId)) : MetaM Unit := do
  let goal :=mkApp (mkConst ``Goal) (mkNatLit n)
  let mvar ← mkFreshExprMVar goal
  let ([mvarId], _) ← Lean.Elab.runTactic mvar.mvarId! (← `(tactic| simp only [Goal, loop, step])).raw {} {}
    | throwError "FAILED!"
  let startTime ← IO.monoNanosNow
  let goals ← k mvarId
  let endTime ← IO.monoNanosNow
  let solveMs := (endTime - startTime).toFloat / 1000000.0
  let startTime ← IO.monoNanosNow
  -- logInfo m!"goals: {goals}"
  for goal in goals do
    let ([], _) ← Lean.Elab.runTactic goal (← `(tactic| grind)).raw {} {}
      | throwError "Could not discharge goal with `grind`: {goal}"
  let endTime ← IO.monoNanosNow
  let grindMs := (endTime - startTime).toFloat / 1000000.0
  if check then
    let startTime ← IO.monoNanosNow
    checkWithKernel (← instantiateExprMVars mvar)
    let endTime ← IO.monoNanosNow
    let kernelMs := (endTime - startTime).toFloat / 1000000.0
    IO.println s!"goal_{n}: {solveMs} ms, grind: {grindMs} ms, kernel: {kernelMs} ms"
  else
    IO.println s!"goal_{n}: {solveMs} ms, grind: {grindMs} ms"

macro "solve" : tactic => `(tactic| {
  intro s post h
  mvcgen' <;> grind
})

def solveUsingMeta (n : Nat) (check := true) : MetaM Unit := do
  driver n check fun mvarId => do
    Prod.fst <$> Lean.Elab.runTactic mvarId (← `(tactic| (intro s post h; mvcgen'))).raw {} {}

def runBenchUsingMeta (sizes : List Nat) : MetaM Unit := do
  IO.println "=== VCGen tests ==="
  IO.println ""
  for n in sizes do
    solveUsingMeta n


set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

-- set_option diagnostics true in
#eval runBenchUsingMeta [1000]

-- set_option diagnostics true in
-- example (p : Nat -> Prop) : p ⊑ wp (loop 300) (fun _ => p) () := by
--   simp only [loop, step]
--   intro s hs
--   mvcgen'
--   grind
