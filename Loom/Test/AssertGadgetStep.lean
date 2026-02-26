import Lean
import Loom.Test.Driver
import Loom.Test.Specs
import Loom.Triple.Gadget
import Loom.Tactic.VCGen

open Loom Lean Meta Order

attribute [lspec high] Spec.assertGadget

instance : Frame (Nat → Prop) := by
  sorry

def step (n : Nat) : StateM Nat Unit := do
  let x ← get
  set (x + n + 1)
  assertGadget (name := none) (· > x)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n + 1 => step n; loop n

def Goal (n : Nat) : Prop :=
  ∀ s, wp (loop n) (fun _ _ => True) ⟨⟩ s

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000


#eval
  runBenchUsingTactic
    ``Goal [``loop, ``step]
    `(tactic| (intro s; mvcgen'))
    `(tactic| sorry)
    [200, 250, 300, 350, 400]
