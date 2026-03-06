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
  by_cases h30 : n = 30
  ·
    let h : Triple _ (throwNatOrString n) (fun _ => True) epost⟨(· = 7), (· = "inner")⟩ := by
      simpa [throwNatOrString, h30, throwThe] using
        (Spec.throw_ExceptT (m := Except String) (err := 7)
          (post := (fun _ => True))
          (epost := epost⟨(· = 7), (· = "inner")⟩))
    exact Triple.iff.mpr <| Triple.entails_wp_of_pre h (by intro _; decide)
  · by_cases h239 : n = 239
    ·
      let h : Triple _ (throwNatOrString n) (fun _ => True) epost⟨(· = 7), (· = "inner")⟩ := by
        simpa [throwNatOrString, h30, h239, throwThe] using
          (Spec.throw_ExceptT_lift (m := Except String) (ε := String) (ε' := Nat)
            (err := "inner")
            (post := (fun _ => True))
            (epost := epost⟨(· = 7), (· = "inner")⟩))
      exact Triple.iff.mpr <| Triple.entails_wp_of_pre h (by intro _; simp)
    ·
      simpa [throwNatOrString, h30, h239] using
        (Spec.pure (m := M) (a := ())
          (post := (fun _ => True))
          (epost := epost⟨(· = 7), (· = "inner")⟩))

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

#eval
  runBenchUsingTactic
    ``Goal [``loop, ``step]
    `(tactic| mvcgen')
    `(tactic| sorry)
    [1000]
