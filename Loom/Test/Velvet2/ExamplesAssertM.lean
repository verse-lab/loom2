import Loom.Test.Velvet2.SyntaxAssertM
import Loom.Triple.Basic
import Loom.Triple.SpecLemmas
import Loom.LatticeExt

/- attribute [-grind] getElem?_neg getElem?_pos getElem!_neg getElem!_pos -/

private theorem prop_true_pre_apply {p : Prop}
    (h : Lean.Order.PartialOrder.rel True p) : p :=
  h True.intro

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
  let h <- guard (i = a.size)
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


#print isGreaterWithInvariants


-- This needs me to figure out the syntactic positions of each of the VCs...
prove_correct isGreaterWithInvariants by
  mvcgen' simplifying_assumptions with grind
  · simp [Loom.InvListWithNames.one, Loom.InvListWithNames.cons]; grind
  · simp [Loom.InvListWithNames.one, Loom.InvListWithNames.cons] at *;
    constructor
    grind; intros; sorry --some simplifications are missing, seeing wp in the goals, which is not something we should see..
  · simp only [Loom.InvListWithNames.one, Loom.InvListWithNames.cons] at *;
    -- seems to be the goal related to decreasing?
    sorry
  · -- again seems to be some goal related to decreasing??? or idk? or invariants??
    simp only [Loom.InvListWithNames.one, Loom.InvListWithNames.cons] at *;
    grind


#eval! (isGreaterWithInvariants 2 #[1]).run
  (AssertM.guard_of_triple (isGreaterWithInvariants_correct 2 #[1]) (by
    unfold Loom.InvListWithNames.one
    decide))

#eval (isGreaterWithInvariants 2 #[1, 3]).run
  (AssertM.guard_of_triple (isGreaterWithInvariants_correct 2 #[1, 3]) (by
    unfold Loom.InvListWithNames.one
    decide))

method guardedAccess (n : Int) (a : Array Int)
  returns (result : Bool)
  requires size_gt_0: a.size > 0
  ensures result = (a[0]! < n)
do
  let h <- guard (0 < a.size)
  return a[0]'(by exact h.proof) < n

prove_correct guardedAccess by
  mvcgen' simplifying_assumptions with grind
  constructor
  · exact size_gt_0
  · intro _h
    exact (Std.Do'.WPMonad.wp_pure (m := AssertM) (decide (a[0] < n))
      (fun result => Loom.InvListWithNames.one `ensures1 ((result = true) = (a[0]! < n)))
      Std.Do'.EPost.nil.mk) (by
        unfold Loom.InvListWithNames.one
        grind)

#eval (guardedAccess 2 #[1]).run
  (AssertM.guard_of_triple (guardedAccess_correct 2 #[1]) (by
    unfold Loom.InvListWithNames.one
    decide))

#info_trees in
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
-- No: under AssertM, this recursive method should not verify from `True`.
-- The old Option-specific proof path made this look provable because it used
-- partial-correctness facts for `Option`; AssertM does not get that rule.
-- prove_correct foo' by
--   mvcgen' simplifying_assumptions with grind
  
  

