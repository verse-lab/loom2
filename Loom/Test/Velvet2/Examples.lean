import Loom.Test.Velvet2.Syntax
import Loom.Triple.Basic
import Loom.Triple.SpecLemmas
import Loom.LatticeExt

/- attribute [-grind] getElem?_neg getElem?_pos getElem!_neg getElem!_pos -/

method isGreaterWithInvariants (n : Int) (a : Array Int)
  returns (result : Bool)
  requires size_gt_0: a.size > 0
  ensures result = true ↔ (∀ i : Nat, i < a.size → a[i]! < n)
do
  let mut ok := true
  let mut i : Nat := 0
  while loop_cond: i < a.size
    invariant sz_invariant: 0 ≤ i ∧ i ≤ a.size
    -- I'd like to be able to access loop_cond here too..
    invariant inv_ok: ok = true ↔ (∀ j : Nat, j < i → a[j]! < n)
    decreasing by_size: a.size - i
    done_with h_done : a.size ≤ i
  do
    if a[i]'(loop_cond) < n then
      ok := ok
    else
      ok := false
    i := i + 1
  return ok

set_option maxHeartbeats 10000000

/- open Std.Do' Loom Lean.Order in
 - prove_correct isGreaterWithInvariants by
 -   apply Triple.intro
 -   apply invlist_one_pre_intro
 -   intros ha
 -   apply prop_pre_elim
 -   unfold wp
 -   apply WP.wp_bind -/




prove_correct isGreaterWithInvariants by
  mvcgen' simplifying_assumptions with grind
  constructor
  intros; grind
  intros; expose_names
  have h' := h i (by grind)
  grind



method isGreaterWithInvariants' (n : Int) (a : Array Int)
  returns (result : Bool)
  requires size_gt_0: a.size > 0
  ensures result = true ↔ (∀ i : Nat, i < a.size → a[i]! < n)
do
  let res <- isGreaterWithInvariants n a
  return res



prove_correct isGreaterWithInvariants' by
  mvcgen' simplifying_assumptions with grind
  --constructor
  --intros; grind
  --intros; expose_names
  --have h' := h i (by grind)
  --grind

#check isGreaterWithInvariants_correct

run_meta do
    let isRec <- Lean.Meta.isRecursiveDefinition `isGreaterWithInvariants
    dbg_trace s!"{isRec}"


method rec foo' (p: Int) returns (res: Int) do
    let res <- foo' (p-1)
    return res

-- Should this really verify?? Very weirddd (even when I change Int -> Nat)
prove_correct foo' by
  mvcgen' simplifying_assumptions with grind
  
  







