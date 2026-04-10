import Loom.Test.Velvet.Syntax

attribute [-grind] getElem?_neg getElem?_pos getElem!_neg getElem!_pos Array.getElem_push

/- Problem Description
    myMin: Determine the minimum of two integers.
    Natural language breakdown:
    1. The input consists of two integers a and b.
    2. The output is an integer result.
    3. The result must be less than or equal to a, and less than or equal to b.
    4. The result must be one of the inputs (either a or b).
    5. When a = b, returning either one is allowed (they are equal).
-/

method myMin (a : Int) (b : Int) return (result : Int)
  ensures result ≤ a
  ensures result ≤ b
  ensures result = a ∨ result = b
  do
    if a <= b then
      return a
    else
      return b

set_option maxHeartbeats 10000000

prove_correct myMin by
  mvcgen' simplifying_assumptions with grind
