import Lean
import Loom.Test.Driver
import Loom.Tactic.VCGen

open Loom Lean Meta Order

abbrev M := ExceptT Nat (Except String)

def throwNatOrString (n : Nat) : M PUnit := do
  if n = 30 then
    throwThe Nat 7
  else if n = 239 then
    throwThe String "inner"
  else
    pure ()

@[lspec high]
theorem spec_throwNatOrString (n : Nat) :
    Triple True (throwNatOrString n) (fun _ => True) epost⟨(· = 7), (· = "inner")⟩ := by
  rw [Triple.iff]; intro; unfold throwNatOrString
  mvcgen' <;> rfl

def step (n : Nat) : ExceptT Nat (Except String) PUnit := do
  throwNatOrString n
  pure ()

def loop (n : Nat) : ExceptT Nat (Except String) PUnit := do
  match n with
  | 0 => pure ()
  | n + 1 =>
    step n
    loop n

def Goal (n : Nat) : Prop :=
  wp (loop n) (fun _ => True) epost⟨(· = 7), (· = "inner")⟩

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

-- set_option trace.Loom.Tactic.vcgen true

def runTests := runBenchUsingTactic
    ``Goal [``loop, ``step]
    `(tactic| mvcgen')
    `(tactic| sorry)

#eval runTests [1000]
