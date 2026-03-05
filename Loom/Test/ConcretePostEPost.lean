import Lean
import Loom.Test.Driver
import Loom.Tactic.VCGen

open Loom Lean Meta Order

/-
Benchmark for the spec-generalization path where both `post` and `epost` are concrete in
an `@[lspec]` theorem. `mvcgen'` must abstract them back out using `WPMonad.wp_cons_econs`.
-/

def concreteGet : StateM Nat Nat := get

@[lspec high]
theorem spec_concreteGet :
    Triple (fun s => s = s) concreteGet (fun x s => x = s) ⟨⟩ := by
  simpa [concreteGet] using
    (Spec.get_StateT
      (m := Id) (l := Prop) (e := EPost.nil)
      (σ := Nat) (post := fun x s => x = s) (epost := ⟨⟩))

def step (n : Nat) : StateM Nat Unit := do
  let x ← concreteGet
  set (x + n + 1)

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
    [1000]
