import Loom.Test.Velvet.Syntax
import Init.Data.Array.Perm

open Std.Do' Lean.Order

attribute [-grind] getElem?_neg getElem?_pos getElem!_neg getElem!_pos

/- Problem Description
    insertionSort: sort an array of natural numbers in non-decreasing order.

    The implementation maintains a sorted prefix `arr[0..n)` and inserts the
    next element by swapping it leftward until it reaches its sorted position.
-/

def Array.toMultiset (arr : Array α) [BEq α] : α → Nat :=
  fun a => arr.count a

@[grind =]
theorem Array.toMultiset_swap_nat
    (arr : Array Nat) (i j : Nat) (hi : i < arr.size) (hj : j < arr.size) :
    ((arr.set! i arr[j]!).set! j arr[i]!).toMultiset = arr.toMultiset := by
  have hset : (arr.set! i arr[j]!).set! j arr[i]! = arr.swap i j hi hj := by
    rw [Array.swap_def]
    simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds_def, hi, hj]
  rw [hset]
  funext x
  unfold Array.toMultiset
  rw [← Array.count_toList (xs := arr.swap i j hi hj) (a := x)]
  rw [← Array.count_toList (xs := arr) (a := x)]
  exact (Array.swap_perm (xs := arr) (i := i) (j := j) hi hj).toList.count_eq x

method insertionSort (arr : Array Nat)
  return (result : Array Nat)
  require 1 ≤ arr.size
  ensures result.toMultiset = arr.toMultiset
  ensures ∀ i j, 0 ≤ i ∧ i < j ∧ j ≤ result.size - 1 → result[i]! ≤ result[j]!
  do
  let mut arr := arr
  let arr₀ := arr
  let arr_size := arr.size
  let mut n := 1
  while' n ≠ arr.size
    invariant size_eq₁ : arr.size = arr_size
    invariant n_bound : 1 ≤ n ∧ n ≤ arr.size
    invariant inner_sorted₁ : ∀ i j, 0 ≤ i ∧ i < j ∧ j ≤ n - 1 → arr[i]! ≤ arr[j]!
    invariant multiset_eq₁ : arr.toMultiset = arr₀.toMultiset
    decreasing arr.size - n
  do
    let mut mind := n
    while' mind ≠ 0
      invariant size_eq₂ : arr.size = arr_size
      invariant mind_bound : mind ≤ n
      invariant inner_sorted₂ : ∀ i j, 0 ≤ i ∧ i < j ∧ j ≤ n ∧ j ≠ mind → arr[i]! ≤ arr[j]!
      invariant multiset_eq₂ : arr.toMultiset = arr₀.toMultiset
      decreasing mind
    do
      if arr[mind]! < arr[mind - 1]! then
        let tmp := arr[mind - 1]!
        arr := arr.set! (mind - 1) arr[mind]!
        arr := arr.set! mind tmp
      mind := mind - 1
    n := n + 1
  return arr

set_option maxHeartbeats 10000000

prove_correct insertionSort by
  mvcgen' simplifying_assumptions with grind
  intro i j; by_cases i < n - 1 <;> grind
