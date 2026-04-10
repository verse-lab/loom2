import Loom.Test.Velvet.Syntax

method testNames (n : Nat)
  return (result : Nat)
  ensures result = 0
  do
  let mut i : Nat := 0
  let mut j : Nat := 0
  let mut k : Nat := 0
  while' i < n
    invariant i ≤ n
    invariant j = 0
    invariant k = 0
  do
    i := i + 1
    j := j
    k := k
  return j

set_option pp.letVarTypes true in
#print testNames

prove_correct testNames by
  mvcgen' simplifying_assumptions
  all_goals trace_state
  all_goals sorry
