import Loom.Test.Velvet.Syntax

attribute [-grind] getElem?_neg getElem?_pos getElem!_neg getElem!_pos Array.getElem_push

/- Problem Description
    sumAndAverage: compute the sum and average of the first n natural numbers.
    Natural language breakdown:
    1. Input n is a natural number.
    2. The sum is the sum of all natural numbers from 0 to n inclusive.
    3. The sum satisfies Gauss' identity: 2 * sum = n * (n + 1).
    4. The output sum is returned as an Int and must be nonnegative.
    5. The average is a Float intended to represent sum / n.
    6. Although the narrative says n is positive, the tests include n = 0.
    7. For n = 0, the output is defined by the tests as (0, 0.0).
    8. For n > 0, the average is defined using Float division of the converted sum by Float.ofNat n.
-/

def gaussSumNat (n : Nat) : Nat :=
  n * (n + 1) / 2


method sumAndAverage' (n: Nat) return (result: Int × Float)
  ensures result.1 = Int.ofNat (gaussSumNat n)
  ensures n = 0 → result.2 = 0.0
  ensures n > 0 → result.2 = (Float.ofInt result.1) / (Float.ofNat n)
  do
  -- Assume there's an implicit tc: [inst: sumAndAverage'.Proofs n]
  -- Then during elaboration:
    let mut idx : Nat := 0
    let mut sm : Nat := 0
    -- ideally should be while (h: <cond>)
    while' idx < n
-- how do we get this in the program context? without having a sorry?
-- The idea would be to bundle up stuff somehow and put it in the context of the runnable program.
-- A way would be to inject a typeclass instance for that..
-- Like how do we say there's this thingy, but we'll prove it later? it's kind of like adding an assume to the thing? is there any mechanism??
        invariant (sm = gaussSumNat idx) 
        invariant (idx <= n)
        done_with (n = idx)
        do
        idx := idx + 1
        sm := sm + idx
    

    let sumNat : Nat := sm
    let sumInt : Int := Int.ofNat sumNat

    if n = 0 then
      return (sumInt, 0.0)
    else
      let avg : Float := (Float.ofInt sumInt) / (Float.ofNat n)
      return (sumInt, avg)

set_option maxHeartbeats 10000000

prove_correct sumAndAverage' by
  mvcgen' simplifying_assumptions with grind
  unfold gaussSumNat; grind
  simp_all; unfold gaussSumNat; simp_all; unfold gaussSumNat; grind
  unfold gaussSumNat at *; grind



method sumAndAverage (n: Nat) return (result: Int × Float)
  ensures result.1 = Int.ofNat (gaussSumNat n)
  ensures n = 0 → result.2 = 0.0
  ensures n > 0 → result.2 = (Float.ofInt result.1) / (Float.ofNat n)
  do
    let sumNat : Nat := gaussSumNat n
    let sumInt : Int := Int.ofNat sumNat

    if n = 0 then
      return (sumInt, 0.0)
    else
      let avg : Float := (Float.ofInt sumInt) / (Float.ofNat n)
      return (sumInt, avg)

set_option maxHeartbeats 10000000

prove_correct sumAndAverage by
  mvcgen' simplifying_assumptions with grind


