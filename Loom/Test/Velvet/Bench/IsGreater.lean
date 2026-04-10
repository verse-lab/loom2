import Loom.Test.Velvet.Syntax

attribute [-grind] getElem?_neg getElem?_pos getElem!_neg getElem!_pos

method isGreater (n : Int) (a : Array Int)
  return (result : Bool)
  require a.size > 0
  ensures result = true ↔ (∀ i : Nat, i < a.size → a[i]! < n)
  do
    let mut ok := true
    let mut i : Nat := 0
    while' i < a.size
      invariant 0 ≤ i ∧ i ≤ a.size
      invariant ok = true ↔ (∀ j : Nat, j < i → a[j]! < n)
    do
      if a[i]! < n then
        ok := ok
      else
        ok := false
      i := i + 1
    return ok

set_option maxHeartbeats 10000000

prove_correct isGreater by
  mvcgen' simplifying_assumptions with grind
