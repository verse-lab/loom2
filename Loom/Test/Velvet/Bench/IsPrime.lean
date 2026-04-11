import Loom.Test.Velvet.Syntax

attribute [-grind] getElem?_neg getElem?_pos getElem!_neg getElem!_pos

/- Problem Description
    isPrime: Determine whether a given natural number is prime.
-/

method isPrime (n : Nat) return (result : Bool)
  require 2 ≤ n
  ensures result = true ↔ ¬ ∃ k : Nat, 1 < k ∧ k < n ∧ n % k = 0
  do
  let mut k : Nat := 2
  let mut composite : Bool := false
  while' k < n ∧ composite = false
    invariant (2 ≤ k ∧ k ≤ n)
    invariant (composite = true → ∃ d : Nat, 1 < d ∧ d < n ∧ n % d = 0)
    invariant (composite = false → ∀ d : Nat, 2 ≤ d ∧ d < k → n % d ≠ 0)
    done_with (k = n ∨ composite = true)
  do
    if n % k = 0 then
      composite := true
    else
      k := k + 1
  if composite = true then
    return false
  else
    return true

set_option maxHeartbeats 10000000

-- prove_correct isPrime by
--   (mvcgen' simplifying_assumptions with grind) <;> sorry
