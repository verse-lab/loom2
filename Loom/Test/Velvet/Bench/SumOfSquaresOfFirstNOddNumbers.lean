import Loom.Test.Velvet.Syntax

attribute [-grind] getElem?_neg getElem?_pos getElem!_neg getElem!_pos Array.getElem_push

/- Problem Description
    sumOfSquaresOfFirstNOddNumbers: Sum of squares of the first n odd natural numbers.
    Natural language breakdown:
    1. The input n is a natural number, so it is non-negative.
    2. The first n odd natural numbers are 1, 3, 5, ..., (2*n - 1).
    3. The desired output is the sum of the squares of these n odd numbers.
    4. The result must match the closed-form value (n * (2*n - 1) * (2*n + 1)) / 3.
    5. The function is total: it must accept any n : Nat.
-/

-- Helper: the numerator of the closed-form expression.
-- We keep this as a separate definition to improve readability.
def oddSquaresClosedFormNumerator (n : Nat) : Nat :=
  n * (2 * n - 1) * (2 * n + 1)

method sumOfSquaresOfFirstNOddNumbers (n : Nat)
  return (result : Nat)
  ensures result = oddSquaresClosedFormNumerator n / 3
  do
    let num := oddSquaresClosedFormNumerator n
    let res := num / 3
    return res

set_option maxHeartbeats 10000000

prove_correct sumOfSquaresOfFirstNOddNumbers by
  mvcgen' simplifying_assumptions with grind
