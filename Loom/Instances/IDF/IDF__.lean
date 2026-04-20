import Loom.Triple.Basic
import Loom.Instances.IDF.IDF_


open Lean.Order Loom

open Classical

set_option autoImplicit false

-- ============================================================================
-- § A. preal basic arithmetic
-- ============================================================================

namespace preal

theorem add_comm (a b : preal) : a + b = b + a := by
  ext; simp; grind

theorem add_assoc (a b c : preal) : (a + b) + c = a + (b + c) := by
  ext; simp; grind

@[simp] theorem zero_add (a : preal) : 0 + a = a := by
  ext; simp; grind

@[simp] theorem add_zero (a : preal) : a + 0 = a := by
  ext; simp; grind

theorem le_refl (a : preal) : a ≤ a := by
  show a.val ≤ a.val; grind

theorem le_trans {a b c : preal} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  show a.val ≤ c.val from Rat.le_trans h₁ h₂

theorem le_antisymm {a b : preal} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  ext; exact Rat.le_antisymm h₁ h₂

theorem ppos_iff_ne_zero (a : preal) : a.ppos ↔ a ≠ 0 := by
  constructor
  · intro hp heq; subst heq; exact absurd hp (by simp [ppos])
  · intro hne
    have : a.val ≠ 0 := fun h => hne (by ext; exact h)
    show 0 < a.val
    have : 0 ≤ a.val := a.nonneg
    grind


theorem zero_not_ppos : ¬ (0 : preal).ppos := by simp [ppos]

theorem ppos_add_left {a b : preal} (h : a.ppos) : (a + b).ppos := by
  show 0 < a.val + b.val; unfold ppos at h;have := b.nonneg; grind

theorem ppos_add_right {a b : preal} (h : b.ppos) : (a + b).ppos := by
  show 0 < a.val + b.val; have := a.nonneg; unfold ppos at h; grind

theorem le_add_right (a b : preal) : a ≤ a + b := by
  show a.val ≤ a.val + b.val; grind [b.nonneg]

theorem le_add_left (a b : preal) : b ≤ a + b := by
  show b.val ≤ a.val + b.val; grind [a.nonneg]

end preal


-- ============================================================================
-- § B. VirtualState: plus/disjoint extended lemmas
-- ============================================================================

namespace VirtualState


theorem stabilize_of_plus_core
    {a c x : VirtualState}
    (h : plus a (c.core) = some x) :
    stabilize x = stabilize a := by
  have hs := stabilize_sum h
  rw [stabilize_core_eq_empty, plus_empty_right] at hs
  exact Option.some.inj (by grind)



/-- Disjoint is symmetric; if `a` and `b` combine, so do `b` and `a`. -/
theorem plus_comm {a b c : VirtualState}
    (h : plus a b = some c) : plus b a = some c := by
  unfold plus at h ⊢
  split at h
  · rename_i hD
    have hD' : Disjoint b a := hD.symm
    simp [hD']
    simp at h
    subst h
    apply VirtualState.ext
    · intro hl
      show b.mask hl + a.mask hl = a.mask hl + b.mask hl
      ext; simp; grind
    · intro hl
      simp [heapMerge]
      cases h1 : a.heap hl with
      | none =>
        cases h2 : b.heap hl with
        | none => rfl
        | some v => rfl
      | some va =>
        cases h2 : b.heap hl with
        | none => rfl
        | some vb =>
          have := hD.1 hl va vb h1 h2
          subst this; rfl
  · exact absurd h (by simp)


theorem Disjoint.assoc_left
    {a b c ab x : VirtualState}
    (hab : plus a b = some ab)
    (hxc : plus ab c = some x) :
    ∃ bc, Disjoint b c ∧ plus b c = some bc ∧ Disjoint a bc ∧ plus a bc = some x := by
  rcases plus_assoc_exists hab hxc with ⟨bc, hbc, hax⟩
  exact ⟨bc, disjoint_of_plus hbc, hbc, disjoint_of_plus hax, hax⟩



 theorem Disjoint.assoc_right
    {a b c bc x : VirtualState}
    (hbc : plus b c = some bc)
    (hax : plus a bc = some x) :
    ∃ ab, Disjoint a b ∧ plus a b = some ab ∧ Disjoint ab c ∧ plus ab c = some x := by
  have hcb : plus c b = some bc := plus_comm hbc
  have hxa : plus bc a = some x := plus_comm hax
  rcases plus_assoc_exists hcb hxa with ⟨ab, hba, hcab⟩
  have hab : plus a b = some ab := plus_comm hba
  have habc : plus ab c = some x := plus_comm hcab
  exact ⟨ab, disjoint_of_plus hab, hab, disjoint_of_plus habc, habc⟩

/-- Empty is disjoint with every well-formed virtual state. -/
theorem Disjoint.empty_right (a : VirtualState) : Disjoint a empty := by
  refine ⟨?_, ?_⟩
  · intro hl v₁ v₂ _ h2; simp [empty] at h2
  · intro hl
    show a.mask hl + empty.mask hl ≤ 1
    simp [empty]; exact a.wf.2 hl

theorem Disjoint.empty_left (a : VirtualState) : Disjoint empty a :=
  (Disjoint.empty_right a).symm

/-- If `a ⊕ b = c` and `a` is empty, then `c = b`. -/
theorem plus_empty_left_eq {b c : VirtualState}
    (h : plus empty b = some c) : c = b := by
  have := plus_empty_left b
  rw [this] at h; exact (Option.some.inj h).symm

theorem plus_empty_right_eq {a c : VirtualState}
    (h : plus a empty = some c) : c = a := by
  have := plus_empty_right a
  rw [this] at h; exact (Option.some.inj h).symm



/-- heapMerge specialized: if left is `none`, take right. -/
theorem heapMerge_none_left {h₁ h₂ : PartialHeap} {hl : HeapLoc}
    (h : h₁ hl = none) : heapMerge h₁ h₂ hl = h₂ hl := by
  simp [heapMerge, h]
  cases h₂ hl <;> rfl

/-- heapMerge specialized: if right is `none`, take left. -/
theorem heapMerge_none_right {h₁ h₂ : PartialHeap} {hl : HeapLoc}
    (h : h₂ hl = none) : heapMerge h₁ h₂ hl = h₁ hl := by
  simp [heapMerge, h]; cases h₁ hl <;> rfl

/-- If both heaps have a value at `hl` and are compatible, they agree. -/
theorem heapMerge_some_some {h₁ h₂ : PartialHeap} {hl : HeapLoc}
    {v₁ v₂ : Val}
    (hc : heapCompatible h₁ h₂)
    (he₁ : h₁ hl = some v₁) (he₂ : h₂ hl = some v₂) :
    heapMerge h₁ h₂ hl = some v₁ := by
  have : v₁ = v₂ := hc hl v₁ v₂ he₁ he₂
  simp [heapMerge, he₁, he₂]

/-- heapCompatible is symmetric. -/
theorem heapCompatible.symm {h₁ h₂ : PartialHeap}
    (h : heapCompatible h₁ h₂) : heapCompatible h₂ h₁ := by
  intro hl v₂ v₁ he₂ he₁; exact (h hl v₁ v₂ he₁ he₂).symm

/-- heapCompatible with empty (everywhere `none`) is trivial. -/
theorem heapCompatible_empty_left (h : PartialHeap) :
    heapCompatible (fun _ => none) h := by
  intro hl v₁ v₂ he₁; simp at he₁

theorem heapCompatible_empty_right (h : PartialHeap) :
    heapCompatible h (fun _ => none) := by
  intro hl v₁ v₂ _ he₂; simp at he₂

/-- Permission at a location is bounded by 1 in any well-formed state. -/
theorem mask_le_one (φ : VirtualState) (hl : HeapLoc) : φ.mask hl ≤ 1 :=
  φ.wf.2 hl

/-- If a location has a value, either it has positive permission, or the
    state is unstable. (Given wfPreVirtualState, value requires... actually
    wf says positive perm → value, not the converse.) -/
theorem heap_some_of_ppos {φ : VirtualState} {hl : HeapLoc}
    (hp : (φ.mask hl).ppos) : (φ.heap hl).isSome :=
  φ.wf.1 hl hp

end VirtualState


-- ============================================================================
-- § C. VirtualState: stabilize/core compositionality
-- ============================================================================

namespace VirtualState

@[simp] theorem stabilize_empty : stabilize empty = empty := by
  apply VirtualState.ext <;> intro hl
  · rfl
  · simp [stabilize, empty, preal.ppos]

@[simp] theorem core_empty : core empty = empty := by
  apply VirtualState.ext <;> intro hl
  · rfl
  · rfl

/-- Stabilize is idempotent. -/
theorem stabilize_stabilize (φ : VirtualState) :
    stabilize (stabilize φ) = stabilize φ := by
  apply stable_eq_stabilize; exact stabilize_stable φ

/-- Stabilize preserves the mask. -/
@[simp] theorem stabilize_getPerm (φ : VirtualState) (hl : HeapLoc) :
    (stabilize φ).getPerm hl = φ.getPerm hl := rfl



/-- Core is idempotent. -/
theorem core_core (φ : VirtualState) : core (core φ) = core φ := by
  apply VirtualState.ext <;> intro hl <;> rfl

/-- A stabilized state's core is the core of the original
    (core erases all permissions anyway, and stabilize keeps values with
    positive permission; the composition matches the pre-stabilized core
    restricted to the ppos locations). -/
theorem core_stabilize (φ : VirtualState) :
    (core (stabilize φ)).heap = (stabilize φ).heap := by
  funext hl; rfl


end VirtualState


-- ============================================================================
-- § D. hProp connectives: hPure, hExists, hForall, hWand
-- ============================================================================
-- Building on the existing `Assertion`, `sep`, `emp`, we introduce the
-- standard SL connectives.

namespace Assertion

/-- Pure assertion: Prop that must hold, on the empty heap only. -/
inductive hPure' (P : Prop) : VirtualState → Prop where
  | intro (HP : P) : hPure' P VirtualState.empty

def hPure (P : Prop) : Assertion := hPure' P

notation:68 "⌜" P "⌝" => hPure P

/-- Existential over heaps. -/
inductive hExists' {α : Type} (P : α → Assertion) (φ : VirtualState) : Prop where
  | intro (a : α) (Ha : P a φ) : hExists' P φ

def hExists {α : Type} (P : α → Assertion) : Assertion := hExists' P

notation:50 "∃ʰ " x ", " P => hExists (fun x => P)

/-- Universal. -/
def hForall {α : Type} (P : α → Assertion) : Assertion := fun φ => ∀ a, P a φ

notation:50 "∀ʰ " x ", " P => hForall (fun x => P)

/-- Magic wand: `H₁ -∗ H₂` witnesses an assertion H such that
    `H ∗ ⌜H₁ ∗ H ⊢ H₂⌝` holds. -/
def hWand (H₁ H₂ : Assertion) : Assertion :=
  ∃ʰ H, H ∗ hPure (H₁ ∗ H ⊢ H₂)


def hWand' (H₁ H₂ : Assertion) : Assertion :=
fun φ => ∀ a b, H₁ a → VirtualState.plus a φ = some b -> H₂ b


theorem hWand_iff_hWand'
    (H₁ H₂ : Assertion) :
    hWand H₁ H₂ = hWand' H₁ H₂ := by
  funext φ
  apply propext
  constructor
  · intro h
    rcases h with ⟨H, a, e, hplus, hHa, hpure⟩
    unfold hPure at hpure
    rcases hpure with ⟨he⟩
    simp[VirtualState.plus_empty_right] at hplus

    subst hplus
    intro x y hHx hxy
    have hxH : (H₁ ∗ H) y := by
      exact ⟨x, _, hxy, hHx, hHa⟩
    apply he
    apply hxH
  · intro hφ
    refine ⟨(fun ψ => ψ = φ), ?_⟩
    refine ⟨φ, VirtualState.empty, ?_, ?_, ?_⟩
    · simpa using VirtualState.plus_empty_right φ
    · rfl
    · constructor
      · intro ψ hsep
        rcases hsep with ⟨a, b, hab, hHa, hbEq⟩
        subst hbEq
        simpa using hφ a ψ hHa hab

infix:60 " -∗ " => hWand

end Assertion


-- ============================================================================
-- § E. Separating conjunction laws
-- ============================================================================

namespace Assertion

/-- `∗` is monotone in the right argument. -/
theorem sep_mono_r {H P Q : Assertion} (hle : P ⊢ Q) : H ∗ P ⊢ H ∗ Q := by
  intro φ h
  rcases h with ⟨φ₁, φ₂, hplus, hH, hP⟩
  exact ⟨φ₁, φ₂, hplus, hH, hle _ hP⟩

/-- `∗` is monotone in the left argument. -/
theorem sep_mono_l {H P Q : Assertion} (hle : P ⊢ Q) : P ∗ H ⊢ Q ∗ H := by
  intro φ h
  rcases h with ⟨φ₁, φ₂, hplus, hP, hH⟩
  exact ⟨φ₁, φ₂, hplus, hle _ hP, hH⟩

/-- Full monotonicity of `∗`. -/
@[grind .]theorem sep_mono {P Q P' Q' : Assertion} (hp : P ⊢ P') (hq : Q ⊢ Q') :
    P ∗ Q ⊢ P' ∗ Q' := by
  intro φ h
  rcases h with ⟨φ₁, φ₂, hplus, hP, hQ⟩
  exact ⟨φ₁, φ₂, hplus, hp _ hP, hq _ hQ⟩

/-- Commutativity of `∗`. -/
theorem sep_comm (P Q : Assertion) : P ∗ Q ⊢ Q ∗ P := by
  intro φ h
  rcases h with ⟨φ₁, φ₂, hplus, hP, hQ⟩
  exact ⟨φ₂, φ₁, VirtualState.plus_comm hplus, hQ, hP⟩

theorem sep_comm_eq (P Q : Assertion) : (P ∗ Q) = (Q ∗ P) := by
  funext φ; apply propext
  exact ⟨fun h => sep_comm P Q φ h, fun h => sep_comm Q P φ h⟩



theorem sep_assoc_l (P Q R : Assertion) : (P ∗ Q) ∗ R ⊢ P ∗ (Q ∗ R) := by
  intro φ h
  rcases h with ⟨φ₁₂, φ₃, h123, h12, hR⟩
  rcases h12 with ⟨φ₁, φ₂, h12, hP, hQ⟩
  rcases VirtualState.plus_assoc_exists h12 h123 with ⟨φ₂₃, h23, h1_23⟩
  exact ⟨φ₁, φ₂₃, h1_23, hP, ⟨φ₂, φ₃, h23, hQ, hR⟩⟩

 theorem sep_assoc_r (P Q R : Assertion) : P ∗ (Q ∗ R) ⊢ (P ∗ Q) ∗ R := by
  intro φ h
  rcases h with ⟨φ₁, φ₂₃, h1_23, hP, h23⟩
  rcases h23 with ⟨φ₂, φ₃, h23, hQ, hR⟩
  have h32 : VirtualState.plus φ₃ φ₂ = some φ₂₃ := VirtualState.plus_comm h23
  have h23_1 : VirtualState.plus φ₂₃ φ₁ = some φ := VirtualState.plus_comm h1_23
  rcases VirtualState.plus_assoc_exists h32 h23_1 with ⟨φ₁₂, h21, h3_12⟩
  have h12 : VirtualState.plus φ₁ φ₂ = some φ₁₂ := VirtualState.plus_comm h21
  have h12_3 : VirtualState.plus φ₁₂ φ₃ = some φ := VirtualState.plus_comm h3_12
  exact ⟨φ₁₂, φ₃, h12_3, ⟨φ₁, φ₂, h12, hP, hQ⟩, hR⟩

 theorem sep_assoc_eq (P Q R : Assertion) : ((P ∗ Q) ∗ R) = (P ∗ (Q ∗ R)) := by
  funext φ
  apply propext
  exact ⟨sep_assoc_l P Q R φ, sep_assoc_r P Q R φ⟩



theorem emp_sep_entail (P : Assertion) : P ⊢ emp ∗ P := by
  intro φ hP
  refine ⟨VirtualState.empty, φ, ?_, ?_, hP⟩
  · exact VirtualState.plus_empty_left φ
  · simp[emp_iff_empty]

theorem emp_sep (P : Assertion) : emp ∗ P ⊢ P := by
  intro φ h
  rcases h with ⟨φ₁, φ₂, hplus, hemp, hP⟩
  simp [emp_iff_empty] at hemp
  have : φ₁ = VirtualState.empty := hemp
  subst this
  have := VirtualState.plus_empty_left_eq hplus
  subst this
  exact hP

theorem sep_emp_entail (P : Assertion) : P ⊢ P ∗ emp := by
  intro φ hP
  refine ⟨φ, VirtualState.empty, ?_, hP, ?_⟩
  · exact VirtualState.plus_empty_right φ
  · simp[emp_iff_empty]



theorem emp_sep_eq (P : Assertion) : (emp ∗ P) = P := by
  funext φ; apply propext
  exact ⟨emp_sep P φ, emp_sep_entail P φ⟩

end Assertion


-- ============================================================================
-- § F. Wand laws and hPure/hExists/hForall utilities
-- ============================================================================

namespace Assertion

/-- Introduction of ⌜True⌝ on the empty heap. -/
theorem hPure_True_empty : hPure True VirtualState.empty :=
  hPure'.intro trivial

/-- ⌜True⌝ is equivalent to `emp`. -/
theorem hPure_True_eq_emp : hPure True = emp := by
  funext φ; apply propext
  constructor
  · intro h; cases h with | intro _ => simp[emp_iff_empty]
  · intro h; simp[emp_iff_empty] at h; have : φ = VirtualState.empty := h; subst this; exact hPure'.intro trivial


/-- Pure elimination on the left of ∗. -/
theorem hPure_sep_elim {P : Prop} {Q : Assertion} : (hPure P : Assertion) ∗ Q ⊢ Q := by
  intro φ h
  rcases h with ⟨φ₁, φ₂, hplus, hP, hQ⟩
  cases hP with
  | intro _ =>
    have := VirtualState.plus_empty_left_eq hplus
    subst this; exact hQ

/-- Existential introduction under ∗. -/
theorem hExists_sep_intro {α : Type} {P : α → Assertion} {H : Assertion} (a : α) :
    H ∗ P a ⊢ H ∗ (∃ʰ x, P x) := by
  intro φ h
  rcases h with ⟨φ₁, φ₂, hplus, hH, hP⟩
  exact ⟨φ₁, φ₂, hplus, hH, ⟨a, hP⟩⟩

/-- Universal elimination under ∗. -/
theorem hForall_sep_elim {α : Type} {P : α → Assertion} {H Q : Assertion} (a : α)
    (hle : H ∗ P a ⊢ Q) : H ∗ hForall P ⊢ Q := by
  intro φ h
  rcases h with ⟨φ₁, φ₂, hplus, hH, hP⟩
  exact hle φ ⟨φ₁, φ₂, hplus, hH, hP a⟩

/-- Forall introduction: if Q entails each instance, Q entails the forall. -/
theorem hForall_intro {α : Type} {P : α → Assertion} {Q : Assertion}
    (h : ∀ a, Q ⊢ P a) : Q ⊢ hForall P :=
  fun φ hQ a => h a φ hQ

/-- Exists elimination: if P a entails Q for every a, (∃ a, P a) entails Q. -/
theorem hExists_elim {α : Type} {P : α → Assertion} {Q : Assertion}
    (h : ∀ a, P a ⊢ Q) : hExists P ⊢ Q := by
  intro φ hx
  rcases hx with ⟨a, hPa⟩
  exact h a φ hPa

/-- Wand introduction: if `H₁ ∗ H₂ ⊢ Q` then `H₂ ⊢ H₁ -∗ Q`. -/
theorem wand_intro {H₁ H₂ Q : Assertion} (hle : H₁ ∗ H₂ ⊢ Q) :
    H₂ ⊢ H₁ -∗ Q := by
  intro φ hH₂
  refine ⟨H₂, ?_⟩
  refine ⟨φ, VirtualState.empty, ?_, hH₂, ?_⟩
  · exact VirtualState.plus_empty_right φ
  · exact hPure'.intro hle

/-- Wand elimination (modus ponens): `H₁ ∗ (H₁ -∗ Q) ⊢ Q`. -/
theorem wand_elim {H₁ Q : Assertion} : H₁ ∗ (H₁ -∗ Q) ⊢ Q := by
  intro φ h
  rcases h with ⟨φ₁, φ₂, hplus, hH₁, hwand⟩
  rcases hwand with ⟨H', hH'⟩
  rcases hH' with ⟨φ₃, φ₄, hplus', hH'φ₃, hpure⟩
  cases hpure with
  | intro hent =>
    have hφ₃_eq_φ₂ := VirtualState.plus_empty_right_eq hplus'
    subst hφ₃_eq_φ₂
    exact hent φ ⟨φ₁, φ₂, hplus, hH₁, hH'φ₃⟩

/-- Wand is monotone in its consequent. -/
theorem wand_mono_r {H P Q : Assertion} (hle : P ⊢ Q) : H -∗ P ⊢ H -∗ Q := by
  intro φ hw
  rcases hw with ⟨H', hH'⟩
  rcases hH' with ⟨φ₁, φ₂, hplus, hH'φ₁, hpure⟩
  cases hpure with
  | intro hent =>
    refine ⟨H', ?_⟩
    refine ⟨φ₁, _, hplus, hH'φ₁, ?_⟩
    exact hPure'.intro (fun φ h => hle _ (hent φ h))

/-- Wand is anti-monotone in its hypothesis. -/
theorem wand_mono_l {H P Q : Assertion} (hle : P ⊢ H) : H -∗ Q ⊢ P -∗ Q := by
  intro φ hw
  rcases hw with ⟨H', hH'⟩
  rcases hH' with ⟨φ₁, φ₂, hplus, hH'φ₁, hpure⟩
  cases hpure with
  | intro hent =>
    refine ⟨H', ?_⟩
    refine ⟨φ₁, _, hplus, hH'φ₁, ?_⟩
    exact hPure'.intro (fun φ h => by
      rcases h with ⟨ψ₁, ψ₂, hp, hP, hH''⟩
      exact hent φ ⟨ψ₁, ψ₂, hp, hle _ hP, hH''⟩)


/-- `hPure True ∗ Q ⊢ Q`. -/
theorem hPure_True_sep_elim {Q : Assertion} : (hPure True : Assertion) ∗ Q ⊢ Q :=
  hPure_sep_elim

/-- `Q ⊢ hPure True ∗ Q` (because `hPure True = emp`). -/
theorem hPure_True_sep_intro {Q : Assertion} : Q ⊢ (hPure True )∗ Q := by
  rw [hPure_True_eq_emp]; exact emp_sep_entail Q

end Assertion


-- ============================================================================
-- § G. Points-to splitting and combining
-- ============================================================================
-- IDF fractional permissions can be split and combined, matching
-- the paper's `hSingleFrac_split` and `hSingleFrac_combine`.

namespace Assertion

/-- A heap with just a single fractional chunk: mask has `p` at `hl` and 0
    elsewhere, heap has value `v` at `hl` and `none` elsewhere.
    This is well-formed when `p ≤ 1`. -/
def singletonState (hl : HeapLoc) (p : preal) (v : Val)
    (hle : p ≤ 1) : VirtualState where
  mask := fun hl' => if hl' = hl then p else 0
  heap := fun hl' => if hl' = hl then some v else none
  wf := by
    refine ⟨?_, ?_⟩
    · intro hl' hp
      by_cases heq : hl' = hl
      · simp [heq]
      · simp [heq] at hp; exact absurd hp preal.zero_not_ppos
    · intro hl'
      by_cases heq : hl' = hl
      · simp [heq]; exact hle
      · show (if hl' = hl then p else 0) ≤ 1
        simp [heq]
        show (0 : preal) ≤ 1
        show (0 : Rat) ≤ 1; decide

/-- Splitting a points-to fraction: `x ↦[p₁+p₂] v ⊣⊢ x ↦[p₁] v ∗ x ↦[p₂] v`. -/
theorem pointsToDirect_split (hl : HeapLoc) (p₁ p₂ : preal) (v : Val)
    (h₁pos : p₁.ppos) (h₂pos : p₂.ppos) (hle : p₁ + p₂ ≤ 1) :
    pointsToDirect hl (p₁ + p₂) v ⊢ pointsToDirect hl p₁ v ∗ pointsToDirect hl p₂ v := by
  intro φ ⟨hppos, hleφ, hheap⟩

  -- 1. Calculate the remaining permission at hl for φ₂
  let rem_val := (φ.mask hl).val - p₁.val
  have hrem_nonneg : 0 ≤ rem_val := by
    change p₁.val + p₂.val ≤ (φ.mask hl).val at hleφ
    have : 0 ≤ p₂.val := p₂.nonneg
    grind
  let rem : preal := ⟨rem_val, hrem_nonneg⟩
  have hrem_le : rem ≤ 1 := by
    have : (φ.mask hl).val ≤ 1 := φ.wf.2 hl
    have : 0 ≤ p₁.val := p₁.nonneg
    show rem_val ≤ 1
    grind

  -- 2. Define the split states
  let φ₂ := singletonState hl rem v hrem_le

  let φ₁ : VirtualState := {
    mask := fun x => if x = hl then p₁ else φ.mask x
    heap := φ.heap
    wf := by
      constructor
      · intro x hpos
        by_cases hx : x = hl
        · subst hx
          change (φ.heap _).isSome
          simp [hheap]
        · simp [hx] at hpos
          exact φ.wf.1 x hpos
      · intro x
        by_cases hx : x = hl
        · subst hx
          simp
          change p₁ ≤ 1
          have : p₁.val + p₂.val ≤ 1 := hle
          have : 0 ≤ p₂.val := p₂.nonneg
          show p₁.val ≤ 1
          grind
        · simp [hx]
          exact φ.wf.2 x
  }

  -- 3. Prove they are disjoint
  have hD : VirtualState.Disjoint φ₁ φ₂ := by
    constructor
    · intro x v1 v2 h1 h2
      by_cases hx : x = hl
      · subst hx
        change (if _ then some v else none) = some v2 at h2
        simp at h2
        change φ.heap _ = some v1 at h1
        rw [hheap] at h1
        simp at h1
        grind
      · change (if x = hl then some v else none) = some v2 at h2
        simp [hx] at h2
    · intro x
      by_cases hx : x = hl
      · subst hx
        simp [φ₂, φ₁, singletonState]
        show p₁ + rem ≤ 1
        have h_eq : p₁.val + rem_val = (φ.mask x).val := by grind
        show (p₁ + rem).val ≤ 1
        unfold preal.val
        simp
        rw [h_eq]
        have := φ.wf.2
        unfold wfMaskSimple at this
        apply this x
      · simp [φ₂, φ₁, singletonState, hx]
        show φ.mask x ≤ 1
        have : φ.mask x ≤ 1 := φ.wf.2 x
        grind

  -- 4. Provide the witnesses and solve the entailment
  refine ⟨φ₁, φ₂, ?_, ?_, ?_⟩
  · show VirtualState.plus φ₁ φ₂ = some φ
    unfold VirtualState.plus
    simp [hD]
    apply VirtualState.ext
    · intro x
      by_cases hx : x = hl
      · subst hx
        simp [φ₁, φ₂, singletonState]
        apply preal.ext
        simp
        grind
      · simp [φ₁, φ₂, singletonState, hx]
    · intro x
      by_cases hx : x = hl
      · subst hx
        show VirtualState.heapMerge φ.heap (fun x => if x = _ then some v else none) x = φ.heap x
        simp [VirtualState.heapMerge, hheap]
      · show VirtualState.heapMerge φ.heap (fun x => if x = hl then some v else none) x = φ.heap x
        simp [hx, VirtualState.heapMerge]
        cases φ.heap x <;> rfl
  · refine ⟨h₁pos, ?_, ?_⟩
    · show p₁ ≤ φ₁.mask hl
      simp [φ₁]
      exact preal.le_refl p₁
    · show φ₁.heap hl = some v
      show φ.heap hl = some v
      exact hheap
  · refine ⟨h₂pos, ?_, ?_⟩
    · show p₂ ≤ φ₂.mask hl
      simp [φ₂, singletonState]
      change p₁.val + p₂.val ≤ (φ.mask hl).val at hleφ
      show p₂.val ≤ rem.val
      have h_rem : rem.val = (φ.mask hl).val - p₁.val := rfl
      rw [h_rem]
      grind
    · show φ₂.heap hl = some v
      simp [φ₂, singletonState]
/-- Combining: `x ↦[p₁] v ∗ x ↦[p₂] v ⊢ x ↦[p₁+p₂] v`
    (when `p₁ + p₂ ≤ 1`). -/
theorem pointsToDirect_combine (hl : HeapLoc) (p₁ p₂ : preal) (v : Val) :
    pointsToDirect hl p₁ v ∗ pointsToDirect hl p₂ v ⊢ pointsToDirect hl (p₁ + p₂) v := by
  intro φ h
  rcases h with ⟨φ₁, φ₂, hplus, ⟨hp₁pos, hp₁le, hφ₁heap⟩, ⟨hp₂pos, hp₂le, hφ₂heap⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · -- p₁ + p₂ is ppos because p₁ is
    exact preal.ppos_add_left hp₁pos
  · -- mask at hl is p₁ + p₂ (actually ≥ p₁ + p₂)
    have hm := VirtualState.plus_mask hplus (hl := hl)
    -- hm : φ.mask hl = φ₁.mask hl + φ₂.mask hl
    -- hp₁le : p₁ ≤ φ₁.mask hl; hp₂le : p₂ ≤ φ₂.mask hl
    show (p₁ + p₂).val ≤ (φ.mask hl).val
    rw [hm]
    show p₁.val + p₂.val ≤ (φ₁.mask hl).val + (φ₂.mask hl).val
    have helper (a b c d : Rat): a <= b -> c <= d -> a + c <= b + d := by
      intros; grind
    apply helper (a:= p₁.val) (b := (φ₁.mask hl).val) (c := p₂.val) (d := (φ₂.mask hl).val)
    exact hp₁le
    exact hp₂le
  · -- value at hl is v
    have hh := VirtualState.plus_heap hplus (hl := hl)
    rw [hh]
    simp [VirtualState.heapMerge, hφ₁heap]

end Assertion


-- ============================================================================
-- § H. Uniqueness of points-to values
-- ============================================================================

namespace Assertion

theorem pointsToDirect_value_unique
    {hl : HeapLoc} {p₁ p₂ : preal} {v w : Val}
    {P Q : Assertion} {φ : VirtualState}
    (hP : (pointsToDirect hl p₁ v ∗ P) φ)
    (hQ : (pointsToDirect hl p₂ w ∗ Q) φ) :
    v = w := by
  rcases hP with ⟨φ₁, φ₂, hplus₁, ⟨_, _, hv₁⟩, _⟩
  rcases hQ with ⟨ψ₁, ψ₂, hplus₂, ⟨_, _, hv₂⟩, _⟩

  have hφheap := VirtualState.plus_heap hplus₁ (hl := hl)
  have hψheap := VirtualState.plus_heap hplus₂ (hl := hl)
  have hleft : φ.heap hl = some v := by
    rw [hφheap]; simp [VirtualState.heapMerge, hv₁]
  have hright : φ.heap hl = some w := by
    rw [hψheap]; simp [VirtualState.heapMerge, hv₂]
  rw [hleft] at hright
  grind

/-- Symmetric variant (points-to on the right of ∗). -/
theorem pointsToDirect_value_unique'
    {hl : HeapLoc} {p₁ p₂ : preal} {v w : Val}
    {P Q : Assertion} {φ : VirtualState}
    (hP : (P ∗ pointsToDirect hl p₁ v) φ)
    (hQ : (Q ∗ pointsToDirect hl p₂ w) φ) :
    v = w := by
  apply pointsToDirect_value_unique (φ := φ) (P := P) (Q := Q)
  · rw [sep_comm_eq]; exact hP
  · rw [sep_comm_eq]; exact hQ




structure HeapM α where
  predTrans : PredTrans Assertion EPost⟨⟩ α
  monotone : predTrans.monotone := by grind

@[grind =] theorem le_hProp_eq_forall (a b : Assertion) : (a ⊑ b) = ∀ h, (a h → b h) := by
    simp [PartialOrder.rel]

@[grind =] theorem le_fun_eq_forall {α} (f g : α → Assertion) : (f ⊑ g) = ∀ a, f a ⊑ g a := by
  simp [PartialOrder.rel]

@[grind =] theorem PredTrans.monotone_eq {l e α} [PartialOrder l] [PartialOrder e] (pt : PredTrans l e α):
    (pt.monotone) =
  ∀ post post' epost epost', epost ⊑ epost' → post ⊑ post' → pt post epost ⊑ pt post' epost'
 := by simp [PredTrans.monotone]

@[grind! .]
theorem HeapM.predTrans_monotone {α } (m : HeapM α) : m.predTrans.monotone := m.monotone

def HeapM.bind {α β} (x : HeapM α) (f : α → HeapM β) : HeapM β :=
  { predTrans := fun post epost => x.predTrans (fun a => (f a).predTrans post epost) epost }

instance : Monad HeapM where
  pure a := { predTrans := fun post _ => post a }
  bind := HeapM.bind

instance : LawfulMonad (HeapM) where
  map_const := rfl
  id_map _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := rfl

def HeapM.pickSuchThat {α} (p : α → Assertion) : HeapM α :=
  { predTrans := fun post _ h => (∃ a, p a h) ∧ ∀ a, p a h → post a h }

def HeapM.exhale (hp : Assertion) : HeapM Unit :=
  { predTrans := fun post _ => hp ∗ post ()
    monotone := by
      intro post post' epost epost' hpost hpost' H
      simp
      revert H
      apply sep_mono
      grind
      grind
    }


/-

acc(p.f) && p.f == 5 ==>  p.f == 5


-/

/-


fun α => P α : state -> Prop

<=> ?

fun α => ∃ Q, Q α ∧ (Q α → P α)


a : α
P a


∃ Q, Q a ∧ (Q a → P )




-/

def rel_stable_assertion (ω: VirtualState) A := Assertion.StableAssert ((fun α => α = ω) ∗ A)

def framed_by (A B : Assertion) := ∀ ω, A ω → VirtualState.Stable ω → rel_stable_assertion ω B



def exInhaleProp (hp : Assertion) (post : Unit → Assertion) := fun φ => ∃ P, P φ ∧ SelfFraming P ∧ framed_by hp P ∧ (P ⊢ hp -∗ post ())

def HeapM.inhale (hp : Assertion) : HeapM Unit :=
--  SelfFraming (hp -* post ()) ∧ framed_by hp (hp-*post ()) ∗ (hp -∗ post ())
  { predTrans := fun post _ => exInhaleProp hp post
    monotone := by
      intro post post' epost epost' hpost hpost' h
      simp_all
      intro P
      obtain ⟨A, hA, hframe, hframed_by, impl⟩ := P
      refine ⟨A, hA, hframe, hframed_by, ?_⟩
      intro ψ hAψ
      obtain ⟨H, ψ₁, ψ₂, hplus, hH, ⟨hfact⟩⟩ := impl ψ hAψ
      refine ⟨H, ψ₁, _, hplus, hH, hPure'.intro ?_⟩
      intro χ hχ
      exact hpost' () χ (hfact χ hχ)
    }


theorem wp_inhale_selfFraming
    (hp : Assertion) (post : Unit → Assertion) :
    SelfFraming (exInhaleProp hp post) := by
  intro φ
  constructor
  ·
    rintro ⟨P, hPφ, hSF, hFB, hEnt⟩
    refine ⟨P, ?_, hSF, hFB, hEnt⟩

    exact (hSF φ).mp hPφ
  ·
    rintro ⟨P, hP_stab, hSF, hFB, hEnt⟩
    refine ⟨P, ?_, hSF, hFB, hEnt⟩
    exact (hSF φ).mpr hP_stab

theorem wp_existential_sound' (hp : Assertion) (post : Unit → Assertion) (ω : VirtualState)
    (hwp : ∃ P, P ω ∧ SelfFraming P ∧ framed_by hp P ∧ (P ⊢ hp -∗ post ()))
    (ω' : VirtualState)
    (hreach : framed_by hp (· = ω) ∧
              ∃ ω_hp, hp ω_hp ∧ VirtualState.plus ω ω_hp = some ω' ∧ ω'.Stable) :
    post () ω' := by
  obtain ⟨P, hPω, _, _, hEnt⟩ := hwp
  obtain ⟨_, ω_hp, hhp, hplus, _⟩ := hreach
  -- Step 1: Apply hEnt at ω
  have hwand : (hp -∗ post ()) ω := hEnt ω hPω
  -- Step 2: Unfold wand (existential style)
  obtain ⟨H, ψ, ψ_empty, hplus_ω, hHψ, hpure⟩ := hwand
  cases hpure with
  | intro hfact =>
    -- ψ_empty = VirtualState.empty (from hPure' constructor)
    -- Now hplus_ω : plus ψ VirtualState.empty = some ω
    have hψ_eq_ω : ψ = ω := by
      have h1 : VirtualState.plus ψ VirtualState.empty = some ψ :=
        VirtualState.plus_empty_right ψ
      exact Option.some.inj (h1.symm.trans hplus_ω)
    rw [hψ_eq_ω] at hHψ
    -- Step 3: Build witness (hp ∗ H) ω'
    -- plus ω ω_hp = some ω', so by commutativity plus ω_hp ω = some ω'
    have hplus_comm : VirtualState.plus ω_hp ω = some ω' :=
      VirtualState.plus_comm hplus   -- or however your comm is stated
    -- Step 4: Apply hfact
    exact hfact ω' ⟨ω_hp, ω, hplus_comm, hhp, hHψ⟩


theorem wp_existential_sound
    (hp : Assertion) (post : Unit → Assertion) (epost : EPost⟨⟩) :
    ((fun ω => (HeapM.inhale hp).predTrans post epost ω) ∗ hp) ⊢ post () := by
  intro w hw
  obtain ⟨ω, ω_hp, hplus, hwp, hhp⟩ := hw
  -- hwp : (inhale hp).predTrans post epost ω
  -- Unfold wp_existential
  obtain ⟨P, hPω, _, _, hEnt⟩ := hwp
  -- Apply the entailment at ω
  have hwand : (hp -∗ post ()) ω := hEnt ω hPω
  -- Unfold the wand
  obtain ⟨H, ψ, ψ_empty, hplus_ω, hHψ, hpure⟩ := hwand
  cases hpure with
  | intro hfact =>
    -- hfact : hp ∗ H ⊢ post ()
    -- ψ_empty = VirtualState.empty, so ψ = ω
    have hψ_eq_ω : ψ = ω :=
      Option.some.inj ((VirtualState.plus_empty_right ψ).symm.trans hplus_ω)
    rw [hψ_eq_ω] at hHψ
    -- Now H ω and we want (hp ∗ H) w to apply hfact
    have hplus_comm : VirtualState.plus ω_hp ω = some w :=
      VirtualState.plus_comm hplus
    exact hfact w ⟨ω_hp, ω, hplus_comm, hhp, hHψ⟩

theorem wp_inhale_framed_by
    (hp : Assertion) (post : Unit → Assertion) (epost : EPost⟨⟩) :
    framed_by hp (fun φ => (HeapM.inhale hp).predTrans post epost φ) := by
  intro w hhp_w hw_Stable
  intro α hα
  obtain ⟨a1, a2, hplus_α, ha1_eq, ha_a2⟩ := hα
  subst ha1_eq
  obtain ⟨P, hP_a2, hSF, hFB, hEnt⟩ := ha_a2
  have hStableP := hFB _ hhp_w hw_Stable
  have hα_in_P : ((fun φ => φ = a1) ∗ P) α := ⟨a1, a2, hplus_α, rfl, hP_a2⟩
  have h_stab := hStableP α hα_in_P
  obtain ⟨b1, b2, hplus_stab, hb1_eq, hP_b2⟩ := h_stab
  subst hb1_eq
  refine ⟨_, b2, hplus_stab, rfl, ?_⟩

  exact ⟨P, hP_b2, hSF, hFB, hEnt⟩



def HeapM.read (x : HeapLoc) : HeapM Val :=
  pickSuchThat fun v h => (h.lookup x).any (·.1 = v)

def HeapM.assign (x : HeapLoc) (v : Val) : HeapM Unit := do
  exhale perm(x)
  inhale (x ↦ v)

def HeapM.alloc (v : Val) : HeapM HeapLoc := do
  let newKey ← pickSuchThat fun l h => h.contains l = false
  inhale (newKey ↦ v)
  return newKey

def HeapM.skip : HeapM Unit :=
  { predTrans := fun post _ => post () }

instance : WPMonad HeapM Assertion EPost⟨⟩ where
  wpTrans x post _ :=  x.predTrans post ⟨⟩
  wp_trans_pure x post _ := by
    intro h post'
    simp_all [pure] <;> constructor
  wp_trans_bind x f post _ := by
    intro h post'
    simp_all [bind, HeapM.bind]
  wp_trans_monotone x := by
    intro post post' epost epost' hpost hpost' H
    simp_all
    unfold HeapM.predTrans
    apply x.monotone
    grind
    grind




theorem HeapM.inhaleAx (hp P : Assertion)
    (hSF : SelfFraming P)
    (hFB : framed_by hp P) :
    ⦃ P ⦄ inhale hp ⦃ fun _ => P ∗ hp ⦄ := by
  constructor
  intro φ hPφ
  refine ⟨P, hPφ, hSF, hFB, ?_⟩
  intro ψ hPψ
  refine ⟨P, ψ, VirtualState.empty, ?_, hPψ, hPure'.intro ?_⟩
  · exact VirtualState.plus_empty_right ψ
  ·
    intro χ ⟨φ₁, φ₂, hplus, hhp, hP⟩
    exact ⟨φ₂ , φ₁, (VirtualState.plus_comm hplus), hP, hhp⟩



end Assertion


-- ============================================================================
-- § I. Self-framing preservation
-- ============================================================================

namespace Assertion

/-- `emp` is self-framing. -/

theorem selfFraming_sep {P Q : Assertion}
    (hP : SelfFraming P) (hQ : SelfFraming Q) : SelfFraming (P ∗ Q) := by
  intro φ
  constructor
  · intro h
    rcases h with ⟨φ₁, φ₂, hplus, hPφ₁, hQφ₂⟩
    refine ⟨VirtualState.stabilize φ₁, VirtualState.stabilize φ₂, ?_, ?_, ?_⟩
    · exact VirtualState.stabilize_sum hplus
    · exact (hP φ₁).mp hPφ₁
    · exact (hQ φ₂).mp hQφ₂
  · intro h
    rcases h with ⟨φ₁, φ₂, hplus, hPφ₁, hQφ₂⟩

    have hdecomp : VirtualState.plus (VirtualState.stabilize φ) (VirtualState.core φ) = some φ := by
      exact VirtualState.decompose_stabilize_pure φ

    obtain ⟨ψ, hψ1, hψ2⟩ :=
      VirtualState.plus_assoc_exists hplus hdecomp

    refine ⟨φ₁, ψ, hψ2, hPφ₁, ?_⟩

    have hstabψ : VirtualState.stabilize ψ = VirtualState.stabilize φ₂ := by
      apply VirtualState.stabilize_of_plus_core
      apply hψ1

    have hQst : Q (VirtualState.stabilize φ₂) := (hQ φ₂).mp hQφ₂
    have : Q (VirtualState.stabilize ψ) := by
      simpa [hstabψ] using hQst
    exact (hQ ψ).mpr this



/-- Pure assertions are self-framing (they only hold on empty heap which is stable). -/
theorem selfFraming_hPure (P : Prop) : SelfFraming (hPure P) := by
      sorry

end Assertion


-- ============================================================================
-- § J. Entailment utilities
-- ============================================================================

namespace Assertion

theorem entails_refl (P : Assertion) : P ⊢ P := fun _ h => h

theorem entails_trans {P Q R : Assertion} (h₁ : P ⊢ Q) (h₂ : Q ⊢ R) : P ⊢ R :=
  fun φ hP => h₂ φ (h₁ φ hP)

theorem entails_antisymm {P Q : Assertion} (h₁ : P ⊢ Q) (h₂ : Q ⊢ P) : P = Q := by
  funext φ; apply propext; exact ⟨h₁ φ, h₂ φ⟩

/-- Consequence rule (pre-strengthening and post-weakening). -/
theorem entails_of_eq_pre_post {P P' Q Q' : Assertion}
    (hpre : P ⊢ P') (hP'Q' : P' ⊢ Q') (hpost : Q' ⊢ Q) : P ⊢ Q :=
  entails_trans hpre (entails_trans hP'Q' hpost)

end Assertion
