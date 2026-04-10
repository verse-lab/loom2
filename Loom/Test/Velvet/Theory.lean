/-
Velvet Theory: partial-correctness loop infrastructure for Option monad programs.
Adapted from Loom/Test/Velvet.lean — removes decreasing/measure requirements.
-/
import Lean
import Loom.Triple.SpecLemmas
import Loom.Test.Specs
import Loom.Tactic.VCGen

open Loom Lean Meta Order Std.Do' Lean.Order

section Loops

/- partial loop from MonoBind and CCPO instances -/
@[specialize, inline]
def Loop.forIn.loop {m : Type u → Type v} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
    (f : Unit → β → m (ForInStep β)) (b : β) : m β := do
  match ← f () b with
    | ForInStep.done b  => pure b
    | ForInStep.yield b => loop f b
  partial_fixpoint

@[inline]
def Loop.forIn {m : Type u → Type v} {β : Type u} [Monad m] [∀ α, CCPO (m α)] [MonoBind m]
    (_ : Lean.Loop) (init : β) (f : Unit → β → m (ForInStep β)) : m β :=
  Loop.forIn.loop f init

@[instance high]
instance {m : Type u → Type v} [md : Monad m] [ccpo : ∀ α, CCPO (m α)] [mono : MonoBind m] :
    ForIn m Lean.Loop Unit where
  forIn {β} _ b f := @Loop.forIn m β md ccpo mono Loop.mk b f

variable {m : Type u → Type v} {Pred : Type u} {EPred : Type u}
  [Monad m] [Assertion Pred] [Assertion EPred] [WP m Pred EPred]
  [∀ α, CCPO (m α)] [MonoBind m]

/-- Partial-correctness loop invariant rule (no decreasing measure required). -/
theorem repeat_inv_partial (f : Unit → β → m (ForInStep β))
    (inv : ForInStep β → Pred) (epost : EPred)
    (init : β)
    (hstep : ∀ b, Triple (inv (ForInStep.yield b)) (f () b)
      (fun | ForInStep.yield b' => inv (ForInStep.yield b')
           | ForInStep.done b' => inv (ForInStep.done b')) epost) :
    Triple (inv (ForInStep.yield init)) (Loop.forIn.loop f init)
      (fun b => inv (ForInStep.done b)) epost := by
  sorry

/-- Partial-correctness loop rule with separate inv/doneWith. -/
theorem repeat_inv_partial_split (f : Unit → β → m (ForInStep β))
    (inv : β → Pred) (doneWith : β → Pred) (epost : EPred)
    (init : β)
    (hstep : ∀ b, Triple (inv b) (f () b)
      (fun | ForInStep.yield b' => inv b'
           | ForInStep.done b' => inv b' ⊓ doneWith b') epost) :
    Triple (inv init) (Loop.forIn.loop f init) (fun b => inv b ⊓ doneWith b) epost :=
  repeat_inv_partial f
    (fun | ForInStep.yield b => inv b | ForInStep.done b => inv b ⊓ doneWith b)
    epost init hstep

/-- Partial-correctness loop rule when done adds no extra info. -/
theorem repeat_inv_partial_simple (f : Unit → β → m (ForInStep β))
    (inv : β → Pred) (epost : EPred)
    (init : β)
    (hstep : ∀ b, Triple (inv b) (f () b)
      (fun | ForInStep.yield b' => inv b'
           | ForInStep.done b' => inv b') epost) :
    Triple (inv init) (Loop.forIn.loop f init) (fun b => inv b) epost :=
  repeat_inv_partial f
    (fun | ForInStep.yield b => inv b | ForInStep.done b => inv b)
    epost init hstep

set_option linter.unusedVariables false in
def invariantGadget (inv : Pred) : m PUnit := pure ⟨⟩
set_option linter.unusedVariables false in
def onDoneGadget {α : Type _} (done : α) : m PUnit := pure ⟨⟩

/-- Spec for `repeat do` loops — partial correctness (no decreasing measure). -/
@[lspec]
theorem Spec.forIn_loop_partial
    {init : β} {f : Unit → β → m (ForInStep β)}
    {inv : β → Pred} {doneWith : β → Pred} {eInv : EPred}
    (step : ∀ b, Triple (inv b) (f () b)
      (fun | ForInStep.yield b' => inv b'
           | ForInStep.done b' => inv b' ⊓ doneWith b') eInv) :
    Triple (inv init) (forIn Loop.mk init fun u b => do
      invariantGadget (inv b)
      onDoneGadget (doneWith b)
      f u b)
      (fun b => inv b ⊓ doneWith b) eInv :=
  sorry

end Loops

-- InvListWithNames, invlist_cons_pre_intro, invlist_one_pre_intro
-- are defined in Loom/Tactic/Intros.lean (to avoid circular imports)

section Fixpoints

/-- Convert `∀ r, f a = some r → pre → post r` into a Triple. -/
theorem triple_from_option_spec {α β : Type}
    {f : α → Option β} {a : α} {pre : Prop} {post : β → Prop}
    (h : ∀ (r : β), f a = some r → pre → post r) :
    Triple pre (f a) (fun r => post r) (True : Prop) := by
  apply Triple.intro
  intro hpre
  show (f a).elim True post
  cases hfa : f a with
  | none => trivial
  | some r => exact h r hfa hpre

/-- Convert `∀ r, x = some r → pre → post r` to `Triple pre x post True`. -/
theorem option_eq_some_to_triple {pre : Prop} {post : β → Prop}
    {x : Option β}
    (h : ∀ r, x = some r → pre → post r) :
    Triple pre x (fun r => post r) (True : Prop) := by
  apply Triple.intro; intro hpre
  show x.elim True post
  cases hx : x with
  | none => trivial
  | some r => exact h r hx hpre

/-- Convert `∀ a r, f a = some r → pre → post r` to `∀ a, Triple pre (f a) post True`. -/
theorem option_spec_to_triple {α β : Type}
    {f : α → Option β} {pre : Prop} {post : β → Prop}
    (h : ∀ (a : α) (r : β), f a = some r → pre → post r)
    (a : α) : Triple pre (f a) (fun r => post r) (True : Prop) :=
  triple_from_option_spec (h a)

/-- Convert `Triple pre x post True` back to `∀ r, x = some r → pre → post r`. -/
theorem triple_to_option_spec {pre : Prop} {post : β → Prop}
    {x : Option β}
    (h : Triple pre x (fun r => post r) (True : Prop)) :
    ∀ r, x = some r → pre → post r := by
  intro r hx hpre
  have hwp := Triple.iff.mp h hpre
  -- hwp : wp x (fun r => post r) True = x.elim True post
  subst hx
  exact hwp

/-- Iff version for converting between Triple and raw option spec. -/
theorem triple_option_iff {pre : Prop} {post : β → Prop} {x : Option β} :
    Triple pre x (fun r => post r) (True : Prop) ↔
    (∀ r, x = some r → pre → post r) :=
  ⟨triple_to_option_spec, option_eq_some_to_triple⟩

end Fixpoints

section ArrayHelpers

@[grind =]
theorem Array.get_set_c [Inhabited α] (i j : Nat) (val : α) (arr : Array α) :
    i < arr.size → (arr.set! j val)[i]! = if i = j then val else arr[i]! := by
  sorry

@[grind =]
theorem Array.getElem!_push [Inhabited α] (i : Nat) (val : α) (arr : Array α) :
  i <= arr.size → (arr.push val)[i]! = if i < arr.size then arr[i]! else val := by
  intro; grind [Array.extract_succ_right]

@[grind .]
theorem take_succ_eq_append_getElem! {i} {l : List α} (h : i < l.length) [Inhabited α] :
  i < l.length →
  l.take (i + 1) = l.take i ++ [l[i]!] := by
  intros; grind [List.take_append_getElem]

@[grind .]
theorem getElem!_of_mem : ∀ {a} {l : List α} [Inhabited α], a ∈ l → ∃ (i : Nat), i < l.length ∧ l[i]! = a := by
  sorry
  -- grind [List.getElem_of_mem]

@[grind .]
theorem List.getElem!_mem [Inhabited α] (i : Nat) (l : List α) :
  i < l.length → l[i]! ∈ l := by
  intro; grind [List.getElem_mem]

-- MProd.fst_eq / MProd.snd_eq moved to Loom/Tactic/Intros.lean

end ArrayHelpers

attribute [-grind] getElem?_neg getElem?_pos getElem!_neg getElem!_pos
