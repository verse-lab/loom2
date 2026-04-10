import Loom.Test.Velvet.Syntax

attribute [-grind] getElem?_neg getElem?_pos getElem!_neg getElem!_pos

/- Problem Description
    lastDigit: extract the last decimal digit of a non-negative integer.
    Natural language breakdown:
    1. Input n is a natural number (hence non-negative by type).
    2. The last digit in base 10 is the remainder when dividing n by 10.
    3. The result must be a natural number between 0 and 9 inclusive.
    4. The returned digit must satisfy: result = n % 10.
-/

method lastDigit (n : Nat) return (result : Nat)
  ensures result = n % 10
  ensures result < 10
  do
    let d := n % 10
    return d

set_option maxHeartbeats 10000000

-- prove_correct lastDigit by
  -- mvcgen' simplifying_assumptions with grind

prove_correct lastDigit by
  mvcgen' simplifying_assumptions with grind
