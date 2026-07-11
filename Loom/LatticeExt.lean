/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Std.Internal.Do.Assertion
universe u v w
@[expose] public section

set_option linter.missingDocs true

namespace Lean.Order

/-!
# Additional Complete Lattice Operations

Extensions to `Lean.Order.CompleteLattice` providing additional operations
needed for program verification.
-/

section LatticeExtensions

attribute [refl] PartialOrder.rel_refl

variable {α : Type u} [CompleteLattice α]

/-- Bottom element of a complete lattice (infimum of all elements) -/
noncomputable def latticeBot : α := inf (fun _ => True)

theorem latticeBot_le (x : α) : latticeBot ⊑ x := by
  apply inf_le
  trivial

end LatticeExtensions

/-!
# Prop Embedding into Partial Order

Embedding propositions into a partial order with top and bottom.
-/

attribute [local instance] Classical.propDecidable in
/-- Pure embedding of propositions into a complete lattice. -/
noncomputable def CompleteLattice.pure {l : Type u} [CompleteLattice l] : Prop → l := fun p =>
  if p then ⊤ else latticeBot

@[inherit_doc CompleteLattice.pure]
scoped notation "⌜" p "⌝" => CompleteLattice.pure p

attribute [local instance] Classical.propDecidable in
@[simp]
theorem trueE (l : Type v) [CompleteLattice l] : ⌜True⌝ = (⊤ : l) := by
  simp [CompleteLattice.pure]

attribute [local instance] Classical.propDecidable in
@[simp]
theorem falseE (l : Type v) [CompleteLattice l] : ⌜False⌝ = (latticeBot : l) := by
  simp [CompleteLattice.pure]

attribute [local instance] Classical.propDecidable in
theorem LE.pure_imp {l : Type u} [CompleteLattice l]
  (p₁ p₂ : Prop) : (p₁ → p₂) → ⌜p₁⌝ ⊑ (⌜p₂⌝ : l) := by
  simp only [CompleteLattice.pure]
  intro h
  split
  case isTrue hp1 =>
    split
    case isTrue => exact PartialOrder.rel_refl
    case isFalse hp2 => exact absurd (h hp1) hp2
  case isFalse =>
    exact latticeBot_le _

attribute [local instance] Classical.propDecidable in
@[simp]
theorem LE.pure_intro {l : Type u} [CompleteLattice l]
  (p : Prop) (h : l) : (⌜p⌝ ⊑ h) = (p → ⊤ ⊑ h) := by
  simp only [CompleteLattice.pure]
  apply propext
  constructor
  · intro hle hp
    simp only [hp, ↓reduceIte] at hle
    exact hle
  · intro himp
    split
    next hp => exact himp hp
    next => exact latticeBot_le _

attribute [local instance] Classical.propDecidable in
/-- Proving `pre ⊑ ⌜p⌝` reduces to proving `p`. -/
theorem le_pure {l : Type u} [CompleteLattice l] (x : l) (p : Prop) : p → x ⊑ ⌜p⌝ :=
  fun hp => by simp [CompleteLattice.pure, hp]; exact le_top x

attribute [local instance] Classical.propDecidable in
/-- Pointwise characterization of `⌜p⌝` on function lattices: `(⌜p⌝ : σ → β) s = (⌜p⌝ : β)`. -/
theorem top_fun_apply {σ : Type v} {β : Type w} [CompleteLattice β] (s : σ) :
    (⊤ : σ → β) s = (⊤ : β) :=
  PartialOrder.rel_antisymm (le_top _) (le_top (α := σ → β) (fun _ => ⊤) s)

theorem bot_fun_apply {σ : Type v} {β : Type w} [CompleteLattice β] (s : σ) :
    (latticeBot : σ → β) s = (latticeBot : β) :=
  PartialOrder.rel_antisymm (latticeBot_le (α := σ → β) (fun _ => latticeBot) s) (latticeBot_le _)

attribute [local instance] Classical.propDecidable in
@[simp] theorem pure_fun_apply
    {σ : Type v} {β : Type w} [CompleteLattice β]
    (p : Prop) (s : σ) :
    (⌜p⌝ : σ → β) s = (⌜p⌝ : β) := by
  unfold CompleteLattice.pure
  split <;> simp [top_fun_apply, bot_fun_apply]

attribute [local instance] Classical.propDecidable in
@[simp]
theorem pure_intro_l {l : Type u} [CompleteLattice l] (p : Prop) (x y : l) :
  (x ⊓ ⌜ p ⌝ ⊑ y) = (p → x ⊑ y) := by
  apply propext
  constructor
  · intro h hp
    have hxy : x ⊓ ⊤ ⊑ y := by simp only [CompleteLattice.pure, hp, ↓reduceIte] at h; exact h
    have hx_le_meet : x ⊑ x ⊓ ⊤ := le_meet x x ⊤ PartialOrder.rel_refl (le_top x)
    exact PartialOrder.rel_trans hx_le_meet hxy
  · intro h
    simp only [CompleteLattice.pure]
    split
    next hp => exact PartialOrder.rel_trans (meet_le_left x ⊤) (h hp)
    next => exact PartialOrder.rel_trans (meet_le_right x latticeBot) (latticeBot_le _)

attribute [local instance] Classical.propDecidable in
@[simp]
theorem pure_intro_r {l : Type u} [CompleteLattice l] (p : Prop) (x y : l) :
  (⌜ p ⌝ ⊓ x ⊑ y) = (p → x ⊑ y) := by
  apply propext
  constructor
  · intro h hp
    have hxy : ⊤ ⊓ x ⊑ y := by simp only [CompleteLattice.pure, hp, ↓reduceIte] at h; exact h
    have hx_le_meet : x ⊑ ⊤ ⊓ x := le_meet x ⊤ x (le_top x) PartialOrder.rel_refl
    exact PartialOrder.rel_trans hx_le_meet hxy
  · intro h
    simp only [CompleteLattice.pure]
    split
    next hp => exact PartialOrder.rel_trans (meet_le_right ⊤ x) (h hp)
    next => exact PartialOrder.rel_trans (meet_le_left latticeBot x) (latticeBot_le _)

/-!
# CompleteLattice instance for Prop

We define a CompleteLattice structure on Prop where:
- rel is implication (→)
- sup is existential quantification over the predicate
-/

theorem loom_prop_pre_intro (x y : Prop) : (x → True ⊑ y) → x ⊑ y :=
  fun h hx => h hx trivial

theorem loom_prop_pre_elim (x : Prop) : x → True ⊑ x :=
  fun hx _ => hx

/-- Intro the left component of a meet precondition: `a ⊓ b ⊑ c` becomes `a → b ⊑ c`. -/
theorem meet_pre_intro (a b c : Prop) : (a → b ⊑ c) → a ⊓ b ⊑ c :=
  fun h hab => h ((meet_le_left a b) hab) ((meet_le_right a b) hab)

/-- Intro the right component of a meet precondition: `a ⊓ b ⊑ c` becomes `a → b ⊑ c`. -/
theorem meet_pre_intro' (a b c : Prop) : (b → a ⊑ c) → a ⊓ b ⊑ c :=
  sorry


/-- Eliminate `True` from the left of a meet precondition. -/
theorem true_meet_pre_elim (b c : Prop) : b ⊑ c → True ⊓ b ⊑ c :=
  fun h hab => h ((meet_le_right True b) hab)

end Lean.Order
