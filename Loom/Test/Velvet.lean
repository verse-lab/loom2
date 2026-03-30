import Lean
import Loom.Test.Driver
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

theorem repeat_inv (f : Unit → β → m (ForInStep β))
    (inv : ForInStep β → Pred) (measure : β → Nat) (epost : EPred)
    (init : β)
    (hstep : ∀ b, Triple (inv (ForInStep.yield b)) (f () b)
      (fun | ForInStep.yield b' => inv (ForInStep.yield b') ⊓ ⌜ measure b' < measure b ⌝
           | ForInStep.done b' => inv (ForInStep.done b')) epost) :
    Triple (inv (ForInStep.yield init)) (Loop.forIn.loop f init)
      (fun b => inv (ForInStep.done b)) epost := by
  have induc (C : β → Prop) (a : β) (h : ∀ x, (∀ y, measure y < measure x → C y) → C x) : C a := by
    have lem : ∀ n : Nat, ∀ x, measure x ≤ n → C x := by
      intro n
      induction n with
      | zero =>
        intro x hx
        exact h x (fun y => by omega)
      | succ m ih =>
        intro x hx
        by_cases neq : measure x ≤ m
        · exact ih x neq
        · exact h x (fun y hy => ih y (by omega))
    exact lem (measure a) a (by simp)
  apply induc
    (fun ini => Triple (inv (ForInStep.yield ini)) (Loop.forIn.loop f ini)
      (fun b => inv (ForInStep.done b)) epost) init
  intro b ih; unfold Loop.forIn.loop
  apply Triple.bind _ _ (fun step => match step with
    | ForInStep.yield b' => inv (ForInStep.yield b') ⊓ ⌜ measure b' < measure b ⌝
    | ForInStep.done b' => inv (ForInStep.done b'))
  · exact hstep b
  · intro step; match step with
    | ForInStep.done b' => exact Triple.pure b' PartialOrder.rel_refl
    | ForInStep.yield b' =>
      apply Triple.iff.mpr
      simp [pure_intro_l]
      intro m_lt
      exact Triple.iff.mp (ih b' m_lt)

/-- Loop rule with invariant incorporated into the body: `inv` lives on `β` directly
(same predicate for yield and done), and an optional `doneWith` strengthening on exit. -/
theorem repeat_inv_split (f : Unit → β → m (ForInStep β))
    (inv : β → Pred) (doneWith : β → Pred) (measure : β → Nat) (epost : EPred)
    (init : β)
    (hstep : ∀ b, Triple (inv b) (f () b)
      (fun | ForInStep.yield b' => inv b' ⊓ ⌜ measure b' < measure b ⌝
           | ForInStep.done b' => inv b' ⊓ doneWith b') epost) :
    Triple (inv init) (Loop.forIn.loop f init) (fun b => inv b ⊓ doneWith b) epost :=
  repeat_inv f
    (fun | ForInStep.yield b => inv b | ForInStep.done b => inv b ⊓ doneWith b)
    measure epost init hstep

/-- Simplified variant when done adds no extra information. -/
theorem repeat_inv_simple (f : Unit → β → m (ForInStep β))
    (inv : β → Pred) (measure : β → Nat) (epost : EPred)
    (init : β)
    (hstep : ∀ b, Triple (inv b) (f () b)
      (fun | ForInStep.yield b' => inv b' ⊓ ⌜ measure b' < measure b ⌝
           | ForInStep.done b' => inv b') epost) :
    Triple (inv init) (Loop.forIn.loop f init) (fun b => inv b) epost :=
  repeat_inv f
    (fun | ForInStep.yield b => inv b | ForInStep.done b => inv b)
    measure epost init hstep

set_option linter.unusedVariables false in
def invariantGadget (inv : Pred) : m PUnit := pure ⟨⟩
@[simp] theorem invariantGadget_eq (inv : Pred) : invariantGadget (m := m) inv = pure ⟨⟩ := rfl
set_option linter.unusedVariables false in
def decreasingGadget (measure : Nat) : m PUnit := pure ⟨⟩
@[simp] theorem decreasingGadget_eq (measure : Nat) : decreasingGadget (m := m) measure = pure ⟨⟩ := rfl
set_option linter.unusedVariables false in
def onDoneGadget {α : Type _} (done : α) : m PUnit := pure ⟨⟩
@[simp] theorem onDoneGadget_eq {α : Type _} (done : α) : onDoneGadget (m := m) done = pure ⟨⟩ := rfl

/-- Spec for `repeat do` loops (`forIn Loop.mk`). -/
@[lspec]
theorem Spec.forIn_loop
    {init : β} {f : Unit → β → m (ForInStep β)}
    {inv : β → Pred} {measure : β → Nat} {doneWith : β → Pred} {eInv : EPred}
    (step : ∀ b, Triple (inv b) (f () b)
      (fun | ForInStep.yield b' => inv b' ⊓ ⌜ measure b' < measure b ⌝
           | ForInStep.done b' => inv b' ⊓ doneWith b') eInv) :
    Triple (inv init) (forIn Loop.mk init f)
      (fun b => inv b ⊓ doneWith b) eInv :=
  repeat_inv_split f inv doneWith measure eInv init step

end Loops

section InsertionSort

def insertionSort (input : List Nat) : Option (List Nat) := do
  let mut sorted : List Nat := []
  let mut unsorted := input
  repeat do
    invariantGadget (sorted.length + unsorted.length = input.length)
    decreasingGadget unsorted.length
    onDoneGadget (unsorted = [])
    match unsorted with
    | [] => break
    | x :: rest =>
      let mut left_rev : List Nat := []
      let mut right := sorted
      repeat do
        invariantGadget (left_rev.reverse ++ right = sorted)
        decreasingGadget right.length
        onDoneGadget True
        match right with
        | [] => break
        | y :: ys =>
          if x ≤ y then break
          left_rev := y :: left_rev
          right := ys
      sorted := left_rev.reverse ++ [x] ++ right
      unsorted := rest
  return sorted


theorem insertionSort_spec (input : List Nat) :
    ⦃ True ⦄ insertionSort input ⦃ result, result.Pairwise (· ≤ ·) ∧ result.Perm input ⦄ := by
  simp only [insertionSort, invariantGadget_eq, decreasingGadget_eq, onDoneGadget_eq, pure_bind]
  mvcgen' -- TODO: gadgets in spec body for automatic inv/measure/doneWith extraction
          -- blocked on backward rule higher-order unification

#eval insertionSort [3, 1, 4, 1, 5, 9, 2, 6]

end InsertionSort
