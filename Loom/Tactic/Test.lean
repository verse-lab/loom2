import Loom.WP.Basic
import Loom.Tactic.VCGen


open Lean Meta Elab Tactic Loom

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
  IO.println "=== VCGen tests == ="
  IO.println ""
  for n in sizes do
    solveUsingMeta n


set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

#eval runBenchUsingMeta [200]

-- -- set_option trace.profiler true in
-- example (p : Nat -> Prop) : Triple p (loop 1000) (fun _ => p) () := by
--   simp only [Triple.iff, loop, step,]
--   intro s hs
--   mvcgen'
--   all_goals sorry
