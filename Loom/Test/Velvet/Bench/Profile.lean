/-
Profiling the 3 outlier benchmarks: DifferenceMinMax, FindEvenNumbers, MergeSorted.
Uses runBenchUsingTactic for timing breakdown + vcgen.grind trace for per-goal times.
-/
import Loom.Test.Driver
import Loom.Test.Velvet.Bench.DifferenceMinMax
import Loom.Test.Velvet.Bench.FindEvenNumbers
import Loom.Test.Velvet.Bench.MergeSorted

open Lean Loom Order Std.Do' Lean.Order

set_option vcgen.time true
set_option trace.Loom.Tactic.vcgen.grind true

-- DifferenceMinMax
def DiffGoal (_n : Nat) := ∀ a : Array Int,
  ⦃ meet (a.size ≠ 0) True ⦄
  differenceMinMax a
  ⦃ result, ∃ mn mx, IsMinOfArray a mn ∧ IsMaxOfArray a mx ∧ result = mx - mn ⦄

#eval runBenchUsingTactic ``DiffGoal [] `(tactic| (
  intro a; simp only [differenceMinMax]
  unfold IsMinOfArray IsMaxOfArray InArray
  mvcgen' simplifying_assumptions with grind
  rename_i b _ _ _ _
  rcases b with ⟨a, ⟨b, c⟩⟩ <;> simp_all only
  grind
)) `(tactic| fail) [0]

-- FindEvenNumbers
def FindEvenGoal (_n : Nat) := ∀ arr : Array Int,
  ⦃ True ⦄
  findEvenNumbers arr
  ⦃ result,
    meet (arr.Sublist result)
    (meet (∀ x, x ∈ result → isEvenInt x = true)
    (meet (∀ x, isEvenInt x = true → result.count x = arr.count x)
          (∀ x, isEvenInt x = false → result.count x = 0))) ⦄

#eval runBenchUsingTactic ``FindEvenGoal [] `(tactic| (
  intro arr; simp only [findEvenNumbers]
  mvcgen' simplifying_assumptions with grind
)) `(tactic| fail) [0]

-- MergeSorted
def MergeGoal (_n : Nat) := ∀ a1 a2 : Array Nat,
  ⦃ meet (MergeSorted.isSorted a1) (MergeSorted.isSorted a2) ⦄
  mergeSorted a1 a2
  ⦃ result,
    meet (result.size = a1.size + a2.size)
    (meet (MergeSorted.isSorted result)
          (∀ v : Nat, result.count v = a1.count v + a2.count v)) ⦄

#eval runBenchUsingTactic ``MergeGoal [] `(tactic| (
  intro a1 a2; simp only [mergeSorted]
  mvcgen' simplifying_assumptions with grind
  all_goals ((try simp); grind [isSorted_le, Array.take_size])
)) `(tactic| fail) [0]
