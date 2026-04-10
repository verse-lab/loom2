import Loom.Test.Velvet.Syntax

method testNames (n : Nat)
  return (result : Nat)
  require h_pos : n > 0
  ensures h_eq : result = 0
  ensures h_le : result ≤ n
  do
  let mut i : Nat := 0
  let mut j : Nat := 0
  let mut k : Nat := 0
  while' i < n
    invariant h_bound : i ≤ n
    invariant h_j : j = 0
    invariant h_k : k = 0
  do
    i := i + 1
    j := j
    k := k
  return j

prove_correct testNames by
  mvcgen' simplifying_assumptions
  all_goals trace_state
  all_goals sorry
