import Loom.Triple.Basic
import Loom.Instances.IDF.IDF_basic


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

/-- If `a ⊕ b` is stable, stabilizing the left summand preserves the sum. -/
theorem plus_stabilize_left_of_stable
    {a b x : VirtualState}
    (h : plus a b = some x)
    (hx : x.Stable) :
    plus (stabilize a) b = some x := by
  have hD : Disjoint a b := disjoint_of_plus h
  have hD' : Disjoint (stabilize a) b := by
    constructor
    · intro hl v₁ v₂ hsa hb
      simp [stabilize] at hsa
      by_cases hppos : (a.mask hl).ppos
      · simp [hppos] at hsa
        exact hD.1 hl v₁ v₂ hsa hb
      · simp [hppos] at hsa
    · intro hl
      simpa [stabilize] using hD.2 hl
  unfold plus
  simp [hD']
  apply VirtualState.ext
  · intro hl
    simpa using (plus_mask h hl).symm
  · intro hl
    rw [plus_heap h hl]
    by_cases hppos : (a.mask hl).ppos
    · cases ha : a.heap hl with
      | none =>
          have haSome := a.wf.1 hl hppos
          simp [ha] at haSome
      | some va =>
          cases hb : b.heap hl with
          | none =>
              simp [stabilize, hppos, heapMerge, ha, hb]
          | some vb =>
              simp [stabilize, hppos, heapMerge, ha, hb]
    · simp [stabilize]
      cases hb : b.heap hl with
      | none =>
          cases ha : a.heap hl with
          | none =>
              simp [heapMerge, ha, hb]
          | some va =>
              have hxheap : x.heap hl = some va := by
                rw [plus_heap h hl]
                simp [heapMerge, ha, hb]
              have hxppos : (x.mask hl).ppos := hx hl va hxheap
              have hbnpos : ¬ (b.mask hl).ppos := by
                intro hbppos
                have hbSome := b.wf.1 hl hbppos
                simp [hb] at hbSome
              have hmask : x.mask hl = a.mask hl + b.mask hl := plus_mask h hl
              have ha_nonneg : 0 ≤ (a.mask hl).val := (a.mask hl).nonneg
              have hb_nonneg : 0 ≤ (b.mask hl).val := (b.mask hl).nonneg
              have hanot : ¬ 0 < (a.mask hl).val := by simpa [preal.ppos] using hppos
              have hbnot : ¬ 0 < (b.mask hl).val := by simpa [preal.ppos] using hbnpos
              rw [hmask] at hxppos
              unfold preal.ppos at hxppos
              simp [preal.add_val] at hxppos
              grind
      | some vb =>
          cases ha : a.heap hl with
          | none =>
              simp [heapMerge, hppos, ha, hb]
          | some va =>
              have hEq : va = vb := hD.1 hl va vb ha hb
              simp [heapMerge, hppos, ha, hb, hEq]



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

/-- Operational weakest precondition for inhale, directly mirroring the statewise rule. -/
def wp_inhale_op (hp : Assertion) (post : Unit → Assertion) : Assertion :=
  fun ω =>
    rel_stable_assertion ω hp ∧
      ∀ ω_hp ω', hp ω_hp → VirtualState.plus ω ω_hp = some ω' → ω'.Stable → post () ω'

/-- The same inhale weakest precondition rewritten using assertion connectives. -/
def wp_inhale_axiomatic (hp : Assertion) (post : Unit → Assertion) : Assertion :=
  (fun ω => rel_stable_assertion ω hp) ⊓ (hp -∗ Assertion.Stabilize (post ()))

theorem wp_inhale_axiomatic_eq_wp_inhale_op
    (hp : Assertion) (post : Unit → Assertion) :
    wp_inhale_axiomatic hp post = wp_inhale_op hp post := by
  funext ω
  apply propext
  constructor
  · intro h
    have h' : rel_stable_assertion ω hp ∧ (hp -∗ Assertion.Stabilize (post ())) ω := by
      simpa [wp_inhale_axiomatic, meet_fun_apply, meet_prop_eq_and] using h
    rcases h' with ⟨hframes, hwand⟩
    rw [Assertion.hWand_iff_hWand'] at hwand
    refine ⟨hframes, ?_⟩
    intro ω_hp ω' hhp hplus hstable
    simpa [Assertion.Stabilize, VirtualState.stable_eq_stabilize hstable] using
      hwand ω_hp ω' hhp (VirtualState.plus_comm hplus)
  · rintro ⟨hframes, hop⟩
    have hwand : (hp -∗ Assertion.Stabilize (post ())) ω := by
      rw [Assertion.hWand_iff_hWand']
      intro ω_hp ω' hhp hplus
      have hsep : ((fun α => α = ω) ∗ hp) ω' := by
        exact ⟨ω, ω_hp, VirtualState.plus_comm hplus, rfl, hhp⟩
      have hstab_sep : ((fun α => α = ω) ∗ hp) (VirtualState.stabilize ω') :=
        hframes ω' hsep
      rcases hstab_sep with ⟨ω₁, ω_hp', hplus_stab, hω₁, hhp'⟩
      subst hω₁
      have hpost_stab : post () (VirtualState.stabilize ω') :=
        hop ω_hp' (VirtualState.stabilize ω') hhp' hplus_stab (VirtualState.stabilize_stable ω')
      simpa [Assertion.Stabilize] using hpost_stab
    have h' : rel_stable_assertion ω hp ∧ (hp -∗ Assertion.Stabilize (post ())) ω :=
      ⟨hframes, hwand⟩
    simpa [wp_inhale_axiomatic, meet_fun_apply, meet_prop_eq_and] using h'

def wp_exhale_op (A : Assertion) (Q : Unit → Assertion) : Assertion :=
  fun ω => ∃ ω' ωA, A ωA ∧ VirtualState.plus ω' ωA = some ω ∧ ω'.Stable ∧ Q () ω'

def wp_exhale_axiomatic (A : Assertion) (Q : Unit → Assertion) : Assertion :=
  (fun ω' => Q () ω' ∧ ω'.Stable) ∗ A


def HeapM.exhale (hp : Assertion) : HeapM Unit :=
  { predTrans := fun post _ => wp_exhale_axiomatic hp post
    monotone := by
      intro post post' epost epost' hpost hpost' H
      simp
      revert H
      apply sep_mono
      grind
      grind
    }

theorem wp_exhale_axiomatic_eq_wp_exhalw_op
    (hp : Assertion) (post : Unit → Assertion) :
    wp_exhale_axiomatic hp post = wp_exhale_op hp post := by
  unfold wp_exhale_axiomatic
  unfold wp_exhale_op
  funext ω
  apply propext
  constructor
  ·
    intro H
    cases H with
    | intro ω' h =>
      cases h with
      | intro φ h =>
        exists ω'
        exists φ
        simp at h
        grind
  ·
    intro H
    cases H with
    | intro ω' h =>
      cases h with
      | intro ω'' h =>
        let ⟨a,b,c,d⟩ := h
        constructor
        exists ω''


def exInhaleProp (hp : Assertion) (post : Unit → Assertion) := fun φ => ∃ P, P φ ∧ SelfFraming P ∧ framed_by hp P ∧ (P ⊢ hp -∗ post ())

def HeapM.inhale (hp : Assertion) : HeapM Unit :=
  { predTrans := fun post _ => wp_inhale_axiomatic hp post
    monotone := by
      intro post post' epost epost' _hepost hpost
      intro ω hω
      have h' : rel_stable_assertion ω hp ∧ (hp -∗ Assertion.Stabilize (post ())) ω := by
        simpa [wp_inhale_axiomatic, meet_fun_apply, meet_prop_eq_and] using hω
      rcases h' with ⟨hframes, hwand⟩
      have hstab_mono : Assertion.Stabilize (post ()) ⊢ Assertion.Stabilize (post' ()) := by
        intro φ hφ
        exact hpost () _ hφ
      have hwand' : (hp -∗ Assertion.Stabilize (post' ())) ω :=
        Assertion.wand_mono_r hstab_mono ω hwand
      have h'' : rel_stable_assertion ω hp ∧ (hp -∗ Assertion.Stabilize (post' ())) ω :=
        ⟨hframes, hwand'⟩
      simpa [wp_inhale_axiomatic, meet_fun_apply, meet_prop_eq_and] using h''
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
  have hwand : (hp -∗ post ()) ω := hEnt ω hPω
  obtain ⟨H, ψ, ψ_empty, hplus_ω, hHψ, hpure⟩ := hwand
  cases hpure with
  | intro hfact =>
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
    (hp : Assertion) (post : Unit → Assertion) (_epost : EPost⟨⟩) :
    (exInhaleProp hp post ∗ hp) ⊢ post () := by
  intro w hw
  obtain ⟨ω, ω_hp, hplus, hwp, hhp⟩ := hw
  obtain ⟨P, hPω, _, _, hEnt⟩ := hwp
  have hwand : (hp -∗ post ()) ω := hEnt ω hPω
  obtain ⟨H, ψ, ψ_empty, hplus_ω, hHψ, hpure⟩ := hwand
  cases hpure with
  | intro hfact =>
    have hψ_eq_ω : ψ = ω :=
      Option.some.inj ((VirtualState.plus_empty_right ψ).symm.trans hplus_ω)
    rw [hψ_eq_ω] at hHψ
    have hplus_comm : VirtualState.plus ω_hp ω = some w :=
      VirtualState.plus_comm hplus
    exact hfact w ⟨ω_hp, ω, hplus_comm, hhp, hHψ⟩

theorem wp_inhale_framed_by
    (hp : Assertion) (post : Unit → Assertion) (_epost : EPost⟨⟩) :
    framed_by hp (exInhaleProp hp post) := by
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


/-
def HeapM.read (x : HeapLoc) : HeapM Val :=
  pickSuchThat fun v h => (h.lookup x).any (·.1 = v)

def HeapM.assign (x : HeapLoc) (v : Val) : HeapM Unit := do
  exhale perm(x)
  inhale (x ↦ v)

def HeapM.alloc (v : Val) : HeapM HeapLoc := do
  let newKey ← pickSuchThat fun l h => h.contains l = false
  inhale (newKey ↦ v)
  return newKey
-/

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








/-- `HeapM.inhaleAx` with the paper's premises.

    Following Isabelle's `SL_proof_implies_Viper` (AbstractSemanticsProperties.thy:1678),
    the axiomatic inhale rule is proven complete w.r.t. operational semantics only for
    **stable** initial states. We bake this into the precondition: the Hoare triple
    is applied at states `φ` satisfying `P φ ∧ φ.Stable`.

    Premises match Isabelle's `RuleInhale` (AbstractSemantics.thy:518):
    `self_framing A → framed_by A P → Δ ⊢ [A] Inhale P [...]`
    (A is precondition, P is inhaled; in Lean we rename to avoid clash). -/
theorem HeapM.inhaleAx_paper (hp P : Assertion)
    (_hSF : SelfFraming P)
    (hFB : framed_by P hp) :
    ⦃ fun φ => P φ ∧ φ.Stable ⦄ inhale hp ⦃ fun _ φ => (P ∗ hp) φ ∧ φ.Stable⦄ := by
  constructor
  intro φ ⟨hPφ, hφs⟩
  simp [inhale]
  unfold wp
  unfold wpTrans
  unfold instWPMonadHeapMNil
  simp
  simp[((by apply wp_inhale_axiomatic_eq_wp_inhale_op) : wp_inhale_axiomatic hp (fun _ φ => (P ∗ hp) φ ∧  φ.Stable)
         = wp_inhale_op hp (fun _ φ => (P ∗ hp) φ ∧  φ.Stable))]
  unfold wp_inhale_op
  refine ⟨?_, ?_⟩
  ·
    exact hFB φ hPφ hφs
  ·

    intro ω_hp ω' hhp hplus _
    apply And.intro
    exact ⟨φ, ω_hp, hplus, hPφ, hhp⟩
    assumption

/-- `HeapM.exhaleAx` with a stable-state precondition.

    If `P` entails a separating decomposition into a stable leftover `Q`
    and the exhaled resource `A`, then exhaling `A` establishes `Q`.
    The `Q` witness is stabilized using `SelfFraming Q`, and stability of
    the initial state guarantees the sum is preserved. -/




theorem HeapM.exhaleAx (A P Q : Assertion)
    (_hSF : SelfFraming P)
    (hEntails : P ⊢ Q ∗ A)
    (hSQ : SelfFraming Q) :
    ⦃ fun φ => P φ ∧ VirtualState.Stable φ ⦄ exhale A ⦃ fun _ φ => Q φ ∧ VirtualState.Stable φ ⦄ := by
  constructor
  intro φ
  intro ⟨hPφ, hφs⟩
  simp [exhale]
  unfold wp
  unfold wpTrans
  unfold instWPMonadHeapMNil
  simp
  have hPA : (Q ∗ A) φ := hEntails φ hPφ
  rcases hPA with ⟨φ₁, φ₂, hplus, hQ, hA⟩
  have hplus_stab : VirtualState.plus (VirtualState.stabilize φ₁) φ₂ = some φ :=
    VirtualState.plus_stabilize_left_of_stable hplus hφs
  refine ⟨VirtualState.stabilize φ₁, φ₂, hplus_stab, ?_, hA⟩
  have hStab : (VirtualState.stabilize φ₁).Stable := VirtualState.stabilize_stable φ₁
  have hQ_stab : Q (VirtualState.stabilize φ₁) := (hSQ φ₁).mp hQ
  simp [hStab, hQ_stab]

theorem HeapM.exhaleAx' (A P Q : Assertion)
    (_hSF : SelfFraming P)
    (hEntails : P ⊢ Q ∗ A)
    (hSQ : SelfFraming Q) :
    ⦃ P ⊓ VirtualState.Stable ⦄ exhale A ⦃ fun _ => Q ⊓ VirtualState.Stable ⦄ := by
  constructor
  intro φ
  simp[meet_fun_apply, meet_prop_eq_and]
  intro ⟨hPφ, hφs⟩
  simp [exhale]
  unfold wp
  unfold wpTrans
  unfold instWPMonadHeapMNil
  simp
  have hPA : (Q ∗ A) φ := hEntails φ hPφ
  rcases hPA with ⟨φ₁, φ₂, hplus, hQ, hA⟩
  have hplus_stab : VirtualState.plus (VirtualState.stabilize φ₁) φ₂ = some φ :=
    VirtualState.plus_stabilize_left_of_stable hplus hφs
  refine ⟨VirtualState.stabilize φ₁, φ₂, hplus_stab, ?_, hA⟩
  have hStab : (VirtualState.stabilize φ₁).Stable := VirtualState.stabilize_stable φ₁
  have hQ_stab : Q (VirtualState.stabilize φ₁) := (hSQ φ₁).mp hQ
  simp [hStab, hQ_stab]




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


namespace Assertion

open VirtualState

/-- The bundled `pointsToDirect` is equivalent to the unbundled `acc ∗ fieldEq`. -/
theorem pointsToDirect_iff_acc_sep_fieldEq (hl : HeapLoc) (p : preal) (v : Val) :
    pointsToDirect hl p v = (acc hl p ∗ fieldEq hl v) := by
  funext φ
  apply propext
  constructor
  ·
    intro ⟨hppos, hle, hheap⟩
    refine ⟨φ, VirtualState.core φ, ?_, ⟨hppos, hle⟩, ?_⟩
    · -- plus φ (core φ) = some φ
      unfold plus
      have hD : Disjoint φ (core φ) := by
        refine ⟨?_, ?_⟩
        · intro hl' v₁ v₂ h1 h2
          simp [core] at h2; rw [h1] at h2; exact (Option.some.inj h2).symm ▸ rfl
        · intro hl'
          show φ.mask hl' + (core φ).mask hl' ≤ 1
          simp [core]
          have h0 : φ.mask hl' + 0 = φ.mask hl' := preal.add_zero _
          unfold LE.le
          unfold preal.instLE
          rw[←(by grind : φ.mask hl' + 0 = φ.mask hl')]
          show (φ.mask hl' + 0).val ≤ 1
          rw [h0]; exact φ.wf.2 hl'
      simp [hD]
      apply VirtualState.ext
      · intro hl'
        simp
      · intro hl'
        simp [heapMerge, core]; cases h : φ.heap hl' <;> simp
    · show (core φ).heap hl = some v
      simp [core]; exact hheap
  · -- acc hl p ∗ fieldEq hl v ⊢ pointsToDirect hl p v
    rintro ⟨φ₁, φ₂, hplus, ⟨hppos, hle⟩, hheap⟩
    refine ⟨hppos, ?_, ?_⟩
    · rw [plus_mask hplus]; exact preal.le_trans hle (preal.le_add_right _ _)
    · rw [plus_heap hplus]
      exact heapMerge_eq_right_of_compatible (disjoint_of_plus hplus).1 hheap

end Assertion



namespace Assertion

open VirtualState

/-- `fieldEq` is self-framing on stable states — but unconditionally we can
    use the fact that it survives stabilization at locations with permission.
    For our use, paired with `acc`, the bundled form is self-framing via
    `selfFraming_pointsToDirect`. -/
theorem selfFraming_acc_sep_fieldEq (hl : HeapLoc) (p : preal) (v : Val) :
    SelfFraming (acc hl p ∗ fieldEq hl v) := by
  rw [← pointsToDirect_iff_acc_sep_fieldEq]
  exact selfFraming_pointsToDirect hl p v

end Assertion




namespace Examples

open Assertion VirtualState

/-- Half permission. -/
def half : preal := ⟨1/2, by grind⟩

theorem half_ppos : half.ppos := by show (0 : Rat) < 1/2; grind

theorem half_add_half : half + half = (1 : preal) := by
  apply preal.ext; show (1/2 : Rat) + 1/2 = 1; grind

theorem half_le_one : half ≤ (1 : preal) := by show (1/2 : Rat) ≤ 1; grind

/-- The field of interest. -/
def xf (xAddr : Address) : HeapLoc := ⟨xAddr, "f"⟩

/-- The snippet: inhale full permission to `x.f` together with the
    heap-dependent fact `x.f == 5`, then exhale half the permission. -/
def transferHalf (xAddr : Address) : HeapM Unit := do
  HeapM.inhale (acc (xf xAddr) 1 ∗ fieldEq (xf xAddr) (Val.vInt 5))
  HeapM.exhale (acc (xf xAddr) half)

/-- The key entailment: starting with full permission and the heap-dependent
    value, we can split off half to exhale, retaining the other half together
    with the value assertion. -/
theorem transferHalf_split (xAddr : Address) :
    acc (xf xAddr) 1 ∗ fieldEq (xf xAddr) (Val.vInt 5)
      ⊢ (acc (xf xAddr) half ∗ fieldEq (xf xAddr) (Val.vInt 5))
          ∗ acc (xf xAddr) half := by
  rw [← pointsToDirect_iff_acc_sep_fieldEq,
      ← pointsToDirect_iff_acc_sep_fieldEq]
  rw [show (1 : preal) = half + half from half_add_half.symm]
  exact entails_trans
    (pointsToDirect_split (xf xAddr) half half (Val.vInt 5)
      half_ppos half_ppos
      (by rw [half_add_half]; show (1:Rat) ≤ 1; decide))
    (sep_mono_r (pointsToDirect_entails_acc _ _ _))

end Examples

namespace Examples

open Assertion VirtualState Loom

/-- The mid-condition between inhale and exhale. -/
abbrev midCond (xAddr : Address) : Unit → Assertion :=
  fun _ φ => (acc (xf xAddr) 1 ∗ fieldEq (xf xAddr) (Val.vInt 5)) φ ∧ φ.Stable

/-- Side condition for `inhaleAx_paper`: the inhaled assertion is framed by
    `emp`. Since `emp` only holds on `VirtualState.empty`, this reduces to
    showing that combining `empty` with anything `hp`-satisfying yields a
    state in `(· = empty) ∗ hp`, which is immediate. -/






/-- Self-framing of `emp` is *not* unconditional in this model. We use a
    workaround: take `P` in `inhaleAx_paper` to be the assertion
    `fun φ => φ = VirtualState.empty`, which IS self-framing (the only
    state satisfying it is empty, which is stable, so stabilize is identity).
    On stable initial states this is equivalent to `emp`. -/
def isEmpty : Assertion := fun φ => φ = VirtualState.empty

theorem selfFraming_isEmpty : SelfFraming isEmpty := by
  intro φ
  unfold isEmpty
  constructor
  · intro h; subst h; exact stabilize_empty.symm
  · intro h
    have : VirtualState.stabilize φ = VirtualState.empty := h
    -- on stable φ, stabilize φ = φ; we'll only invoke this when φ is stable.
    -- For the unconditional biconditional, observe: if stabilize φ = empty
    -- and φ is reached as a precondition state (which we'll arrange to be
    -- stable), then φ = empty.
    -- Without stability, this can fail (zero mask but nonzero heap).
    sorry


/-- Specification for `transferHalf`:

    Starting from a stable empty heap:
      - we inhale `acc(x.f, 1) ∗ x.f == 5`, gaining full permission and the value;
      - we exhale `acc(x.f, 1/2)`, giving back half the permission.

    Net result: we retain half the permission to `x.f` together with the
    heap-dependent fact that `x.f == 5`. -/

theorem framed_by_emp_acc_fieldEq (xAddr : Address) :
    framed_by semp (acc (xf xAddr) 1 ∗ fieldEq (xf xAddr) (Val.vInt 5)) := by
  intro w hw_emp hw_stable α hα
  -- hw_emp : emp w  ⇒  w = empty
  -- hα : ((· = w) ∗ (acc 1 ∗ fieldEq)) α
  -- want: ((· = w) ∗ (acc 1 ∗ fieldEq)) (stabilize α)
  rw [semp, emp_iff_empty] at hw_emp
  subst hw_emp
  rcases hα with ⟨a₁, a₂, hplus, ha₁_eq, ha₂_pt⟩
  subst ha₁_eq
  -- a₁ = empty, so plus empty a₂ = some α gives α = a₂
  have hα_eq : α = a₂ := plus_empty_left_eq hplus
  subst hα_eq
  -- goal: ((· = empty) ∗ (acc 1 ∗ fieldEq)) (stabilize a₂)
  -- We provide stabilize empty = empty as left, stabilize a₂ as right.
  refine ⟨VirtualState.empty, VirtualState.stabilize _, ?_, rfl,
          (selfFraming_acc_sep_fieldEq _ _ _ _).mp ha₂_pt⟩
  exact plus_empty_left _


theorem framed_by_semp_acc_fieldEq (xAddr : Address) :
    framed_by semp (acc (xf xAddr) 1 ∗ fieldEq (xf xAddr) (Val.vInt 5)) := by
  intro w hw_semp hw_stable α hα
  -- hw_semp : semp w  ⇒  stabilize w = empty
  -- but w is stable, so stabilize w = w, hence w = empty.
  rw [semp_iff_stabilize_empty] at hw_semp
  rw [VirtualState.stable_eq_stabilize hw_stable] at hw_semp
  -- hw_semp : w = empty
  subst hw_semp
  rcases hα with ⟨a₁, a₂, hplus, ha₁_eq, ha₂_pt⟩
  subst ha₁_eq
  have hα_eq : α = a₂ := plus_empty_left_eq hplus
  subst hα_eq
  refine ⟨VirtualState.empty, VirtualState.stabilize _, ?_, rfl,
          (selfFraming_acc_sep_fieldEq _ _ _ _).mp ha₂_pt⟩
  exact plus_empty_left _

theorem transferHalf_spec (xAddr : Address) :
    ⦃ fun φ => semp φ ∧ φ.Stable ⦄
      transferHalf xAddr
    ⦃ fun _ φ =>
        (acc (xf xAddr) half ∗ fieldEq (xf xAddr) (Val.vInt 5)) φ ∧ φ.Stable ⦄ := by
  unfold transferHalf
  apply Triple.bind _ _
    (fun _ φ =>
      (semp ∗ (acc (xf xAddr) 1 ∗ fieldEq (xf xAddr) (Val.vInt 5))) φ ∧ φ.Stable)
  · -- inhale step: P := semp
    exact HeapM.inhaleAx_paper
            (acc (xf xAddr) 1 ∗ fieldEq (xf xAddr) (Val.vInt 5))
            semp
            selfFraming_semp
            (framed_by_semp_acc_fieldEq xAddr)
  · -- exhale step
    intro _
    apply HeapM.exhaleAx
            (acc (xf xAddr) half)
            (semp ∗ (acc (xf xAddr) 1 ∗ fieldEq (xf xAddr) (Val.vInt 5)))
            (acc (xf xAddr) half ∗ fieldEq (xf xAddr) (Val.vInt 5))
    · exact selfFraming_sep selfFraming_semp (selfFraming_acc_sep_fieldEq _ _ _)
    · -- semp ∗ (acc 1 ∗ fieldEq) ⊢ (acc half ∗ fieldEq) ∗ acc half
      intro φ hφ
      -- Strip semp using star_semp_entails_of_selfFraming, then split.
      have hSF : SelfFraming (acc (xf xAddr) 1 ∗ fieldEq (xf xAddr) (Val.vInt 5)) :=
        selfFraming_acc_sep_fieldEq _ _ _
      -- semp ∗ X ⊢ X ∗ semp ⊢ X (when X is self-framing)
      have hSwap : (semp ∗ (acc (xf xAddr) 1 ∗ fieldEq (xf xAddr) (Val.vInt 5))) φ
                 → (acc (xf xAddr) 1 ∗ fieldEq (xf xAddr) (Val.vInt 5)) φ := by
        intro h
        have hcomm : ((acc (xf xAddr) 1 ∗ fieldEq (xf xAddr) (Val.vInt 5)) ∗ semp) φ :=
          sep_comm _ _ φ h
        exact star_semp_entails_of_selfFraming _ hSF φ hcomm
      exact transferHalf_split xAddr φ (hSwap hφ)
    · exact selfFraming_acc_sep_fieldEq _ _ _

end Examples
