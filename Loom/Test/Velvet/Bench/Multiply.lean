import Loom.Test.Velvet.Syntax

attribute [-grind] getElem?_neg getElem?_pos getElem!_neg getElem!_pos Array.getElem_push

/-
Problem Description:
  multiply: Multiply two integers.
  Natural language breakdown:
  1. The input consists of two integers a and b.
  2. The output is an integer representing the arithmetic product of a and b.
  3. There are no restrictions on inputs (they may be negative, zero, or positive).
  4. The result is uniquely determined by integer multiplication.
-/

method multiply (a : Int) (b : Int)
  return (result : Int)
  ensures result = a * b
  do
  let prod := a * b
  return prod

set_option maxHeartbeats 10000000

prove_correct multiply by
  mvcgen' simplifying_assumptions with grind
