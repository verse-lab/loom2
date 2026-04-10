import Loom.Test.Velvet.Syntax

method simpleMethod (n : Nat)
  return (result : Nat)
  require h_pos : n > 0
  ensures h_eq : result = n
  do
  let mut i := 0
  while' i < n
    invariant h_bound : i ≤ n
  do
    i := i + 1
  return i

prove_correct? simpleMethod
