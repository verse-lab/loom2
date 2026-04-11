import Loom.Test.Velvet.Syntax
-- import Mathlib.Data.Nat.Prime.Defs
attribute [-grind] getElem?_neg getElem?_pos getElem!_neg getElem!_pos

method IsNonPrime (n: Nat)
  return (result: Bool)
  ensures True  -- result ↔ ¬Nat.Prime n  (needs Mathlib)
  do
    if n ≤ 1 then
      return true
    let mut i: Nat := 2
    let mut ret: Bool := false
    while' i * i ≤ n
    invariant 2 ≤ i
    invariant (ret = false ↔ ∀ d, 2 ≤ d ∧ d < i → n % d ≠ 0)
    invariant (i - 1) * (i - 1) ≤ n
    -- invariant i ≤ n
    -- decreasing (n + 1 - i)
    do
      if n % i = 0 then
        ret := true
      i := i + 1
    return ret

-- ------------------------------------------------
-- -- Program verification
-- ------------------------------------------------

prove_correct IsNonPrime by
  mvcgen' simplifying_assumptions with grind
