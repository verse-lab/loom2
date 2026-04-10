import Lean

-- import Loom.Test.Velvet.Theory

set_option diagnostics true
set_option trace.profiler true

set_option linter.unusedVariables false

-- @[grind =]
-- theorem Array.getElem!_push [Inhabited α] (i : Nat) (val : α) (arr : Array α) :
--   i <= arr.size → (arr.push val)[i]! = if i < arr.size then arr[i]! else val := by
--   intro; grind [Array.extract_succ_right]

example (arr₁ arr₂ : Array Nat)
  (i n : Nat)
  (arr₂_sorted : ∀ (i j : Nat), i < j → j < arr₂.size → arr₂[i]! ≤ arr₂[j]!)
  (arr₁_arr₂ : 0 < arr₁.size → n < arr₂.size → arr₁[arr₁.size - 1]! ≤ arr₂[n]!)
  (arr₁_sorted : ∀ (i j : Nat), i < j → j < arr₁.size → arr₁[i]! ≤ arr₁[j]!)
  (arr₁_size : arr₁.size = i + n)
  (arr₂_size : n < arr₂.size)
  (k j : Nat)
  (h₁ : k < j)
  (h₂ : j < arr₁.size + 1)
  (le₁ : k < arr₁.size)
  (le₂ : ¬j < arr₁.size)
  (eq : ¬k = arr₁.size - 1) : arr₁[k]! ≤ arr₁[arr₁.size - 1]! := by
  grind

-- example (arr₁ arr₂ : Array Nat)
--   (i n : Nat)
--   (arr₂_sorted : ∀ (i j : Nat), i < j → j < arr₂.size → arr₂[i]! ≤ arr₂[j]!)
--   (arr₁_arr₂ : 0 < arr₁.size → n < arr₂.size → arr₁[arr₁.size - 1]! ≤ arr₂[n]!)
--   (arr₁_sorted : ∀ (i j : Nat), i < j → j < arr₁.size → arr₁[i]! ≤ arr₁[j]!)
--   (arr₁_size : arr₁.size = i + n)
--   (arr₂_size : n < arr₂.size)
--   :
--   ∀ (i j : Nat), i < j → j < arr₁.size + 1 → (arr₁.push arr₂[n]!)[i]! ≤ (arr₁.push arr₂[n]!)[j]! := by
--   grind 

def foo (arr₁ arr₂ : Array Nat) (i n : Nat)
  (arr₂_sorted : ∀ (i j : Nat), i < j → j < arr₂.size → arr₂[i]! ≤ arr₂[j]!)
  (arr₁_arr₂ : 0 < arr₁.size → n < arr₂.size → arr₁[arr₁.size - 1]! ≤ arr₂[n]!)
  (arr₁_sorted : ∀ (i j : Nat), i < j → j < arr₁.size → arr₁[i]! ≤ arr₁[j]!)
  (arr₁_size : arr₁.size = i + n)
  (arr₂_size : n < arr₂.size)
  :
  ∀ (i j : Nat), i < j → j < arr₁.size + 1 → (arr₁.push arr₂[n]!)[i]! ≤ (arr₁.push arr₂[n]!)[j]! := by
  intros k j h₁ h₂
  rw [Array.getElem!_push] <;> try grind [-getElem!_neg]
  rw [Array.getElem!_push] <;> try grind [-getElem!_neg]
  split <;> try grind [-getElem!_neg]
  rename_i le₁
  split <;> try grind [-getElem!_neg]
  rename_i le₂
  apply Nat.le_trans; rotate_left
  apply arr₁_arr₂
  grind [-getElem!_neg]
  grind [-getElem!_neg]
  by_cases eq :k = arr₁.size - 1 
  grind [-getElem!_neg]
  -- clear arr₁_arr₂
  grind -- [-getElem!_neg]
  -- clear arr₁_arr₂  arr₂_size le₂ h₁ h₂ arr₁_size
  -- grind [-Array.getElem!_push]
  -- grind +splitImp
  -- apply arr₁_sorted
  -- grind -- [-getElem!_neg, -getElem?_neg, -getElem?_pos, -getElem!_pos]
  -- grind -- [-getElem!_neg, -getElem?_neg, -getElem?_pos, -getElem!_pos]


