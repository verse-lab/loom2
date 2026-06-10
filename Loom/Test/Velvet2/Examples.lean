import Loom.Test.Velvet2.Syntax
import Loom.Triple.Basic
import Loom.Triple.SpecLemmas
import Loom.LatticeExt
import Loom.Test.Velvet2.GhostM

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
 -   apply named_prop_one_pre_intro
 -   intros ha
 -   apply prop_pre_elim
 -   unfold wp
 -   apply WP.wp_bind -/


#print isGreaterWithInvariants

prove_correct isGreaterWithInvariants by
  mvcgen' simplifying_assumptions  with grind
  all_goals
    simp [Loom.NamedProp.one] at *
    try grind
  · exact ⟨i, by grind⟩



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


method rec foo' (p: Int)
returns (res: Int) 
requires True
ensures True do
    let res <- foo' (p-1)
    return res

-- Should this really verify?? Very weirddd (even when I change Int -> Nat)
prove_correct foo' by
  mvcgen' simplifying_assumptions with grind
  

method get_idx returns (res: Nat)
    ensures res = 1
    do
        return 1

prove_correct get_idx by
    mvcgen' simplifying_assumptions with grind


method isGreaterWithInvariants'' (n : Int) (a : Array Int)
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

#print isGreaterWithInvariants''

#check StateM


open Std.Do'
def one : Option Nat:= do
    pure 1
set_option trace.Loom.Tactic.vcgen true
set_option trace.Loom.Tactic.vcgen.grind true
set_option trace.Loom.Tactic.vcgen.simp true
/- theorem one_correct : Triple (True) one (fun x => x = 1) True :=by
 -     simp only [one]
 -     skip
 -     mvcgen' with grind -/
    

def incr1 : StateT Nat Id Unit:= do
    let cur <- get
    set (cur + 1)

/- theorem incr1_correct
 -     : Triple (fun s => s = 1) (incr1) (fun u s => s = 2) EPost.nil.mk := by
 -     simp only [incr1]
 -     mvcgen' with grind -/

theorem rel_fun_prop_intro {σ : Type} (f g : σ → Prop) :
    (∀ s, Lean.Order.PartialOrder.rel (f s) (g s)) → Lean.Order.PartialOrder.rel f g := by
  intro h
  exact h

theorem spec_bind_intro_state {α β : Type} (pre : Prop)
    (x : StateT Nat Id α) (f : α → StateT Nat Id β)
    (post : β → Nat → Prop) (epost : EPost.nil) (s : Nat) :
    Lean.Order.PartialOrder.rel pre (wp x (fun a => wp (f a) post epost) epost s) →
      Lean.Order.PartialOrder.rel pre (wp (x >>= f) post epost s) := by
  intro h
  exact (Triple.entails_wp_of_pre (Std.Do'.Spec.bind x f) h) s

abbrev BalM α := StateT Nat Id α

def withdraw (amt: Nat) (curBal: Erased Nat) : StateT Nat Id Nat:= do
    let bal <- get
    assert hCurBalUnchanged: (fun s => curBal.reveal = s)
    if bal > amt then
       let newAmt := bal - amt
       let _ <- set newAmt
       assert hChanged : (fun s => s = (curBal.reveal - amt))
       pure newAmt
    else
        pure bal



    
theorem withdraw_correct : ∀ ( amt: Nat ) ( curBal: Erased Nat ),
       Triple (fun s => s = curBal.reveal) (withdraw amt curBal)
              (fun s res =>
                   (s = res) ∧
                    ((curBal.reveal > amt ∧ s = curBal.reveal - amt)
                                    ∨ (curBal.reveal = s)
                    )) EPost.nil.mk := by
        simp only [withdraw]
        intro amt curBal
        sym =>
          -- unfoldTriple
          apply Triple.intro
          -- introsExcessArgs
          apply rel_fun_prop_intro
          intro s
          -- classifyGoal returns .IntroPre
          -- we run the case for .IntroPre in `solve` in VCGen.lean, which calls `introMeetPre`
 /-
  else if !pre.isConstOf ``True then
    match ← rules.propPreIntro.apply goal with
    | .goals [goal'] =>
      let .goal _ goal'' ← Sym.intros goal' | return goal'
      return goal''
    | _ => return goal
 -/
          apply Lean.Order.prop_pre_intro
          intro hs
          -- we are back to classifying the goal
          -- pre is True, so we check the RHS, which is a wp, so this is the .WPMonad case
          -- The program head is `Bind.bind`, so VCGen finds `Spec.bind`
          sorry

          



set_option maxHeartbeats 10000000

/- prove_correct isGreaterWithInvariants'' by
 -     mvcgen' -/
