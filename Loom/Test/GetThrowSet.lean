import Lean
import Loom.Test.Driver
import Loom.Test.Specs
import Loom.Tactic.VCGen

open Loom Lean Meta Order

abbrev M := ExceptT String <| StateM Nat

@[lspec high] theorem spec_throw (e : String) {post : α → Nat → Prop} {epost : EPost⟨String → Nat → Prop⟩} :
    Triple (epost.1 e) (throw (m := M) e) post epost := ⟨PartialOrder.rel_refl⟩

@[lspec high] theorem spec_set (x : Nat) {post : PUnit → Nat → Prop} {epost : EPost⟨String → Nat → Prop⟩} :
    Triple (fun _ => post ⟨⟩ x) (set (m := M) x) post epost := ⟨PartialOrder.rel_refl⟩

@[lspec high] theorem spec_get (post : Nat → Nat → Prop) {epost : EPost⟨String → Nat → Prop⟩} :
    Triple (fun s => post s s) (get (m := M)) post epost := ⟨PartialOrder.rel_refl⟩

def step (lim : Nat) : ExceptT String (StateM Nat) Unit := do
  let s ← get
  if s > lim then
    throw "s is too large"
  set (s + 1)

def loop (n : Nat) : ExceptT String (StateM Nat) Unit := do
  match n with
  | 0 => pure ()
  | n+1 => loop n; step n

def Goal (n : Nat) : Prop := ∀ post epost, post n → wp (loop n) (fun _ => post) epost 0

set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

-- example : Goal 10 := by
--   intro post epost h
--   mvcgen'
--   all_goals sorry
/-
time spent unfolding: 60 ms
goal_400: 161 ms, 401 VCs by sorry: 269 ms, instantiate: 474 ms, shareCommon: 527 ms, kernel: 479 ms
time spent unfolding: 58 ms
goal_500: 205 ms, 501 VCs by sorry: 472 ms, instantiate: 973 ms, shareCommon: 976 ms, kernel: 745 ms
time spent unfolding: 70 ms
goal_600: 263 ms, 601 VCs by sorry: 616 ms, instantiate: 1565 ms, shareCommon: 1251 ms, kernel: 991 ms
time spent unfolding: 98 ms
goal_700: 313 ms, 701 VCs by sorry: 817 ms, instantiate: 2009 ms, shareCommon: 1734 ms, kernel: 1313 ms
time spent unfolding: 115 ms
goal_800: 364 ms, 801 VCs by sorry: 1165 ms, instantiate: 3123 ms, shareCommon: 2394 ms, kernel: 1648 ms
time spent unfolding: 126 ms
goal_900: 402 ms, 901 VCs by sorry: 1516 ms, instantiate: 4287 ms, shareCommon: 3440 ms, kernel: 2117 ms
time spent unfolding: 150 ms
goal_1000: 479 ms, 1001 VCs by sorry: 1967 ms, instantiate: 5486 ms, shareCommon: 4516 ms, kernel: 2485 ms
-/

#eval
  runBenchUsingTactic
    ``Goal [``loop, ``step]
    `(tactic| (intro post epost h; mvcgen'))
    `(tactic| sorry)
    [400, 450, 500, 550, 600, 700]
