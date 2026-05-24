import Std.Tactic
import Loom.Triple.Basic

open Lean.Order Std.Do'

abbrev Loc := Nat
abbrev Val := Int

/-! ## Finite function heaps -/

def Heap := { f : Loc → Option Val // ∃ bound : List Loc, ∀ l, l ∉ bound → f l = none }

namespace Heap

def get? (h : Heap) (x : Loc) : Option Val := h.val x

def contains (h : Heap) (x : Loc) : Bool := (h.get? x).isSome

def empty : Heap := ⟨fun _ => none, ⟨[], by simp⟩⟩

instance : EmptyCollection Heap := ⟨empty⟩
instance : Inhabited Heap := ⟨∅⟩

@[ext]
theorem ext_get? {h₁ h₂ : Heap} (h : ∀ x : Loc, h₁.get? x = h₂.get? x) : h₁ = h₂ := by
  apply Subtype.ext
  funext x
  exact h x

@[simp] theorem get?_empty (x : Loc) : (∅ : Heap).get? x = none := rfl
@[simp] theorem contains_empty (x : Loc) : (∅ : Heap).contains x = false := rfl

@[simp] theorem contains_eq_true {h : Heap} {x : Loc} :
    h.contains x = true ↔ ∃ v, h.get? x = some v := by
  unfold contains
  cases h.get? x <;> simp

@[simp] theorem contains_eq_false {h : Heap} {x : Loc} :
    h.contains x = false ↔ h.get? x = none := by
  unfold contains
  cases h.get? x <;> simp

def insert (h : Heap) (x : Loc) (v : Val) : Heap :=
  ⟨fun y => if x = y then some v else h.get? y,
   by
    rcases h.property with ⟨bound, hbound⟩
    refine ⟨x :: bound, ?_⟩
    intro l hl
    simp [get?]
    have hxl : x ≠ l := by
      intro hxl
      exact hl (by simp [hxl])
    have hlb : l ∉ bound := by
      intro hb
      exact hl (by simp [hb])
    simp [hxl, hbound l hlb]⟩

@[simp] theorem get?_insert_self (h : Heap) (x : Loc) (v : Val) :
    (h.insert x v).get? x = some v := by
  simp [insert, get?]

@[simp] theorem get?_insert (h : Heap) (x y : Loc) (v : Val) :
    (h.insert x v).get? y = if x = y then some v else h.get? y := rfl

@[simp] theorem contains_insert (h : Heap) (x y : Loc) (v : Val) :
    (h.insert x v).contains y = (x == y || h.contains y) := by
  unfold contains
  by_cases hxy : x = y
  · simp [insert, get?, hxy]
  · simp [insert, get?, hxy]

def single (x : Loc) (v : Val) : Heap := (∅ : Heap).insert x v

def union (h₁ h₂ : Heap) : Heap :=
  ⟨fun x => (h₂.get? x).or (h₁.get? x),
   by
    rcases h₁.property with ⟨b₁, hb₁⟩
    rcases h₂.property with ⟨b₂, hb₂⟩
    refine ⟨b₁ ++ b₂, ?_⟩
    intro l hl
    have hl₁ : l ∉ b₁ := fun hmem => hl (List.mem_append_left _ hmem)
    have hl₂ : l ∉ b₂ := fun hmem => hl (List.mem_append_right _ hmem)
    simp [get?, hb₁ l hl₁, hb₂ l hl₂]⟩

@[simp] theorem get?_union (h₁ h₂ : Heap) (x : Loc) :
    (h₁.union h₂).get? x = (h₂.get? x).or (h₁.get? x) := rfl

@[simp] theorem contains_union (h₁ h₂ : Heap) (x : Loc) :
    (h₁.union h₂).contains x = (h₁.contains x || h₂.contains x) := by
  unfold contains
  simp [get?_union]
  cases h₁.get? x <;> cases h₂.get? x <;> simp

/- Disjointness says the domains do not overlap. -/
def Disjoint (h₁ h₂ : Heap) : Prop :=
  ∀ x y, h₁.contains x → h₂.contains y → x ≠ y

@[simp] theorem empty_union (h : Heap) : (∅ : Heap).union h = h := by
  apply Heap.ext_get?
  intro x
  change (h.get? x).or none = h.get? x
  cases h.get? x <;> rfl

@[simp] theorem union_empty (h : Heap) : h.union (∅ : Heap) = h := by
  apply Heap.ext_get?
  intro x
  change none.or (h.get? x) = h.get? x
  cases h.get? x <;> rfl

@[simp] theorem union_assoc (a b c : Heap) : (a.union b).union c = a.union (b.union c) := by
  apply Heap.ext_get?
  intro x
  simp only [get?_union]
  cases a.get? x <;> cases b.get? x <;> cases c.get? x <;> rfl

theorem Disjoint.empty_left (h : Heap) : Heap.Disjoint ∅ h := by
  intro x _ hx _
  simp at hx

theorem Disjoint.empty_right (h : Heap) : Heap.Disjoint h ∅ := by
  intro _ y _ hy
  simp at hy

theorem Disjoint.assoc_left {h₁ h₂ h₃ : Heap}
    (h₁₂ : Heap.Disjoint h₁ h₂) (h₁₂_₃ : Heap.Disjoint (h₁.union h₂) h₃) :
    Heap.Disjoint h₁ (h₂.union h₃) ∧ Heap.Disjoint h₂ h₃ := by
  constructor
  · intro x y hx hy
    rw [Heap.contains_union] at hy
    simp only [Bool.or_eq_true] at hy
    cases hy with
    | inl h₂y => exact h₁₂ x y hx h₂y
    | inr h₃y =>
      exact h₁₂_₃ x y (by rw [Heap.contains_union]; simp [hx]) h₃y
  · intro x y hx hy
    exact h₁₂_₃ x y (by rw [Heap.contains_union]; simp [hx]) hy

theorem Disjoint.assoc_right {h₁ h₂ h₃ : Heap}
    (h₁_₂₃ : Heap.Disjoint h₁ (h₂.union h₃)) (h₂₃ : Heap.Disjoint h₂ h₃) :
    Heap.Disjoint h₁ h₂ ∧ Heap.Disjoint (h₁.union h₂) h₃ := by
  constructor
  · intro x y hx hy
    exact h₁_₂₃ x y hx (by rw [Heap.contains_union]; simp [hy])
  · intro x y hx hy
    rw [Heap.contains_union] at hx
    simp only [Bool.or_eq_true] at hx
    cases hx with
    | inl h₁x => exact h₁_₂₃ x y h₁x (by rw [Heap.contains_union]; simp [hy])
    | inr h₂x => exact h₂₃ x y h₂x hy

theorem Disjoint.not_contains_left {h₁ h₂ : Heap} {x : Loc}
    (hdisj : Heap.Disjoint h₁ h₂) (hx : h₂.contains x) : ¬ h₁.contains x := by
  intro h₁x
  exact absurd rfl (hdisj x x h₁x hx)

theorem Disjoint.insert_val {h : Heap} {x : Loc} {u v : Val}
    (hdisj : Heap.Disjoint h ((∅ : Heap).insert x u)) :
    Heap.Disjoint h ((∅ : Heap).insert x v) := by
  intro a b ha hb
  have hbu : ((∅ : Heap).insert x u).contains b := by
    simp at hb ⊢
    exact hb
  exact hdisj a b ha hbu

theorem Disjoint.single_of_not_contains {h : Heap} {x : Loc} {v : Val}
    (hnot : ¬ h.contains x) : Heap.Disjoint h ((∅ : Heap).insert x v) := by
  intro a b ha hb
  simp at hb
  subst hb
  intro heq
  subst heq
  exact hnot ha

theorem union_insert_eq (h : Heap) (x : Loc) (u v : Val)
    (_hdisj : ¬ h.contains x) :
    (h.union ((∅ : Heap).insert x u)).insert x v = h.union ((∅ : Heap).insert x v) := by
  apply Heap.ext_get?
  intro y
  by_cases hxy : x = y
  · subst hxy
    simp [get?, union, insert]
  · have hyx : y ≠ x := fun h => hxy h.symm
    simp [get?, union, insert, hxy]

theorem insert_eq_union_single (h : Heap) (x : Loc) (v : Val)
    (_hnot : ¬ h.contains x) :
    h.insert x v = h.union ((∅ : Heap).insert x v) := by
  apply Heap.ext_get?
  intro y
  by_cases hxy : x = y
  · subst hxy
    simp [get?, union, insert]
  · simp [get?, union, insert, hxy]
    cases h.get? y <;> rfl

/-! Fresh allocation support. -/

noncomputable def support (h : Heap) : List Loc := Classical.choose h.property

theorem mem_support_of_get?_ne_none {h : Heap} {x : Loc} (hx : h.get? x ≠ none) :
    x ∈ h.support := by
  unfold support
  have hbound := Classical.choose_spec h.property
  by_cases hmem : x ∈ Classical.choose h.property
  · exact hmem
  · exact False.elim (hx (hbound x hmem))

noncomputable def maxKey (h : Heap) : Loc := h.support.max?.getD 0

theorem mem_le_maxKey {h : Heap} {x : Loc} (hx : x ∈ h.support) : x ≤ h.maxKey := by
  unfold maxKey
  cases hs : h.support with
  | nil =>
    rw [hs] at hx
    simp at hx
  | cons y ys =>
    have hmax : (y :: ys).max? = some ((y :: ys).max?.getD 0) := by
      rfl
    have hall := (List.max?_eq_some_iff.mp hmax).2
    exact hall x (by simpa [hs] using hx)

theorem maxKey_not_mem (h : Heap) (x : Loc) :
    x > h.maxKey → ¬ h.contains x := by
  intro hgt hx
  have hxsome : h.get? x ≠ none := by
    rcases (contains_eq_true.mp hx) with ⟨v, hv⟩
    intro hnone
    simp [hnone] at hv
  have hmem : x ∈ h.support := mem_support_of_get?_ne_none hxsome
  have hle : x ≤ h.maxKey := mem_le_maxKey hmem
  exact Nat.not_lt_of_ge hle hgt

end Heap

inductive HeapException : Type where
  | notFound (x : Loc)

/-
   { x ↦ 1 } set ∅ { x ↦ 1 }
  --------------------------
    { hemp } set ∅ { hemp }
-/
abbrev HeapM := StateT Heap (Except HeapException)
abbrev hProp := Heap → Prop
abbrev eProp := HeapException → Prop

@[simp] private theorem Except.apply_wp (x : Except ε α) (post : α → Prop)
    (epost : EPost⟨ε → Prop⟩) :
    wp x post epost = match x with
      | .ok a => post a
      | .error e => epost.head e := rfl

/-! ## Separation assertions -/

inductive hStar' (H₁ : hProp) (H₂ : hProp) (h : Heap) : Prop where
  | intro (h₁ h₂ : Heap) (Hh₁ : H₁ h₁) (Hh₂ : H₂ h₂)
    (h_union : h₁.union h₂ = h)
    (h_disjoint : h₁.Disjoint h₂) :
    hStar' H₁ H₂ h

def hStar (H₁ : hProp) (H₂ : hProp) : hProp := hStar' H₁ H₂

infix:65 " ∗ " => hStar

inductive hExists' (P : α → hProp) (h : Heap) : Prop where
  | intro (a : α) (Ha : P a h) : hExists' P h

def hExists (P : α → hProp) : hProp := hExists' P

notation:50 "∃ʰ " x ", " P => hExists (fun x => P)

def hForall' (P : α → hProp) (h : Heap) : Prop := ∀ a, P a h

def hForall (P : α → hProp) : hProp := hForall' P

notation:50 "∀ʰ " x ", " P => hForall (fun x => P)

inductive hPure' (P : Prop) : Heap → Prop where
  | intro (HP : P) : hPure' P ∅

def hPure (P : Prop) : hProp := hPure' P

notation:68 "⌜" P "⌝ʰ" => hPure P

def hWand (H₁ : hProp) (H₂ : hProp) : hProp := ∃ʰ H, H ∗ hPure (H₁ ∗ H ⊑ H₂)

infix:60 " -∗ " => hWand

inductive hSingle' (x : Loc) (v : Val) : Heap → Prop where
  | intro : hSingle' x v ((∅ : Heap).insert x v)

def hSingle (x : Loc) (v : Val) : hProp := hSingle' x v

notation:70 x " ↦ " v => hSingle x v

def hEmpty : hProp := (· = ∅)

instance : EmptyCollection hProp := ⟨hEmpty⟩

/-! ## Abstract lemmas about hProp connectives -/

theorem hForall_elim {P : α → hProp} (a : α) :
  P a ⊑ Q → hForall P ⊑ Q :=
  fun himp _ hall => himp _ (hall a)

theorem hForall_star_elim {P : α → hProp} (a : α) :
  H ∗ P a ⊑ Q → H ∗ hForall P ⊑ Q := by
  intro hle h ⟨h₁, h₂, hH, hP, hunion, hdisj⟩
  exact hle h (hStar'.intro h₁ h₂ hH (hP a) hunion hdisj)

theorem hForall_intro {P : α → hProp} {Q : hProp}
    (h : ∀ a, Q ⊑ P a) : Q ⊑ hForall P :=
  fun heap hQ a => h a heap hQ

theorem hStar_hPure_true_left {Q : hProp} : hPure True ∗ Q ⊑ Q := by
  intro h ⟨_, h₂, hpure, hQ, hunion, _⟩
  cases hpure with
  | intro _ =>
    rw [Heap.empty_union] at hunion
    exact hunion ▸ hQ

theorem hWand_hPure_true_elim {Q : hProp} : hWand (hPure True) Q ⊑ Q := by
  intro h ⟨H', ⟨h₁, _, hH', hpure, hunion, _⟩⟩
  cases hpure with
  | intro hent =>
    rw [Heap.union_empty] at hunion
    subst hunion
    exact hent h₁ (hStar'.intro ∅ h₁ (hPure'.intro trivial) hH'
      (Heap.empty_union h₁) (Heap.Disjoint.empty_left h₁))

theorem entails_hWand {H₁ H₂ Q : hProp} (hle : H₁ ∗ H₂ ⊑ Q) :
    H₂ ⊑ hWand H₁ Q := by
  intro h hH₂
  exact hExists'.intro H₂ (hStar'.intro h ∅ hH₂ (hPure'.intro hle)
    (Heap.union_empty h) (Heap.Disjoint.empty_right h))

theorem hWand_mono :
  P ⊑ Q → H -∗ P ⊑ H -∗ Q := by
  intro hle h ⟨H', ⟨h₁, h₂, hH', hpure, hunion, hdisj⟩⟩
  cases hpure with
  | intro hent =>
    exact hExists'.intro H' (hStar'.intro h₁ ∅ hH' (hPure'.intro (PartialOrder.rel_trans hent hle))
      hunion hdisj)

theorem hStar_mono :
  P ⊑ Q → H ∗ P ⊑ H ∗ Q := by
  intro hle h ⟨h₁, h₂, hH, hP, hunion, hdisj⟩
  exact hStar'.intro h₁ h₂ hH (hle h₂ hP) hunion hdisj

theorem hWand_elim {H Q : hProp} : H ∗ (H -∗ Q) ⊑ Q := by
  intro h ⟨h₁, h₂, hH, ⟨H', ⟨h₃, h₄, hH', hpure, hunion₂, hdisj₂⟩⟩, hunion, hdisj⟩
  cases hpure with
  | intro hent =>
    rw [Heap.union_empty] at hunion₂
    subst hunion₂
    exact hent h (hStar'.intro h₁ h₃ hH hH' hunion hdisj)

theorem hStar_assoc_l {A B C : hProp} : (A ∗ B) ∗ C ⊑ A ∗ (B ∗ C) := by
  intro h ⟨h₁₂, h₃, ⟨h₁, h₂, hA, hB, hunion₁₂, hdisj₁₂⟩, hC, hunion, hdisj⟩
  have ⟨hdisj₁, hdisj₂⟩ := Heap.Disjoint.assoc_left hdisj₁₂ (hunion₁₂ ▸ hdisj)
  exact hStar'.intro h₁ (h₂.union h₃) hA (hStar'.intro h₂ h₃ hB hC rfl hdisj₂)
    (by rw [← Heap.union_assoc, hunion₁₂, hunion]) hdisj₁

theorem hStar_assoc_r {A B C : hProp} : A ∗ (B ∗ C) ⊑ (A ∗ B) ∗ C := by
  intro h ⟨h₁, h₂₃, hA, ⟨h₂, h₃, hB, hC, hunion₂₃, hdisj₂₃⟩, hunion, hdisj⟩
  have ⟨hdisj₁, hdisj₂⟩ := Heap.Disjoint.assoc_right (hunion₂₃ ▸ hdisj) hdisj₂₃
  exact hStar'.intro (h₁.union h₂) h₃ (hStar'.intro h₁ h₂ hA hB rfl hdisj₁) hC
    (by rw [Heap.union_assoc, hunion₂₃, hunion]) hdisj₂

/-! ## Heap operations -/

def HeapM.assign (x : Loc) (v : Val) : HeapM Unit := do
  if (← get).contains x then do
    modify (·.insert x v)
  else throw (.notFound x)

def HeapM.read (x : Loc) : HeapM Val := do
  match (← get).get? x with
  | some v => pure v
  | none => throw (.notFound x)

noncomputable def HeapM.alloc (v : Val) : HeapM Loc := do
  let newKey := (← get).maxKey + 1
  modify fun h : Heap => h.insert newKey v
  return newKey

/-! ## Layer 1: HeapM computation lemmas -/

@[simp] private theorem HeapM.bind_apply (x : HeapM α) (f : α → HeapM β) (s : Heap) :
    (x >>= f) s = x s >>= fun (a, s') => f a s' := rfl

@[simp] private theorem HeapM.get_apply (s : Heap) :
    (get : HeapM Heap) s = .ok (s, s) := rfl

@[simp] private theorem HeapM.pure_apply (a : α) (s : Heap) :
    (pure a : HeapM α) s = .ok (a, s) := rfl

@[simp] private theorem HeapM.throw_apply (e : HeapException) (s : Heap) :
    (throw e : HeapM α) s = .error e := rfl

@[simp] private theorem HeapM.modify_apply (f : Heap → Heap) (s : Heap) :
    (modify f : HeapM PUnit) s = .ok ((), f s) := rfl

@[simp] private theorem HeapM.map_apply (f : α → β) (x : HeapM α) (s : Heap) :
    (f <$> x) s = x s >>= fun (a, s') => .ok (f a, s') := rfl

/-! ## Layer 2: Inner specs with frame using the base StateT WPMonad instance. -/

theorem HeapM.read_inner (x : Loc) (v : Val) (H : hProp)
    (epost : EPost⟨HeapException → Prop⟩) :
    Triple
      (H ∗ (x ↦ v)) (read x) (fun r => H ∗ (⌜r = v⌝ʰ ∗ x ↦ v)) epost := by
  rw [Triple.iff]
  intro s ⟨h₁, h₂, hH, hSingle, hunion, hdisj⟩
  cases hSingle
  subst hunion
  rw [StateT.apply_wp]
  rw [Except.apply_wp]
  simp [HeapM.read, Heap.get?_union, Heap.get?_insert_self]
  exact hStar'.intro h₁ ((∅ : Heap).insert x v) hH
    (hStar'.intro ∅ ((∅ : Heap).insert x v) (hPure'.intro rfl) hSingle'.intro
      (Heap.empty_union _) (Heap.Disjoint.empty_left _))
    rfl hdisj

theorem HeapM.assign_inner (x : Loc) (v u : Val) (H : hProp)
    (epost : EPost⟨HeapException → Prop⟩) :
    Triple
      (H ∗ (x ↦ u)) (HeapM.assign x v) (fun _ => H ∗ (x ↦ v)) epost := by
  rw [Triple.iff]
  intro s ⟨h₁, h₂, hH, hSingle, hunion, hdisj⟩
  cases hSingle
  subst hunion
  have hcontains : (h₁.union ((∅ : Heap).insert x u)).contains x = true := by
    rw [Heap.contains_union]
    simp
  rw [StateT.apply_wp]
  rw [Except.apply_wp]
  simp [HeapM.assign, hcontains]
  rw [Heap.union_insert_eq h₁ x u v (hdisj.not_contains_left (by simp))]
  exact hStar'.intro h₁ ((∅ : Heap).insert x v) hH hSingle'.intro rfl (hdisj.insert_val)

theorem HeapM.alloc_inner (v : Val) (H : hProp)
    (epost : EPost⟨HeapException → Prop⟩) :
    Triple
      (H ∗ ∅) (HeapM.alloc v) (fun loc => H ∗ (loc ↦ v)) epost := by
  rw [Triple.iff]
  intro s ⟨h₁, h₂, hH, hempty, hunion, _hdisj⟩
  change h₂ = ∅ at hempty
  subst hempty
  rw [Heap.union_empty] at hunion
  subst hunion
  rw [StateT.apply_wp]
  rw [Except.apply_wp]
  change match HeapM.alloc v h₁ with
    | .ok (loc, s') => (H ∗ loc ↦ v) s'
    | .error e => epost.head e
  simp [HeapM.alloc, HeapM.get_apply, HeapM.modify_apply]
  change (H ∗ ((h₁.maxKey + 1) ↦ v)) (h₁.insert (h₁.maxKey + 1) v)
  have hnot : ¬ h₁.contains (h₁.maxKey + 1) :=
    Heap.maxKey_not_mem h₁ _ (by simp)
  rw [Heap.insert_eq_union_single h₁ _ v hnot]
  exact hStar'.intro h₁ ((∅ : Heap).insert _ v) hH hSingle'.intro rfl
    (Heap.Disjoint.single_of_not_contains hnot)

/-! ## Layer 3: Outer separation logic specs -/

instance HeapM.instWPMonadFrame : WPMonad HeapM hProp EPost⟨HeapException → Prop⟩ where
  wpTrans x := ⟨fun post epost => ∀ʰ H, H -∗ wp x (fun x => H ∗ post x) epost⟩
  wp_trans_pure x := by
    intro post epost
    apply hForall_intro
    intro H
    apply entails_hWand
    letI : WPMonad HeapM (Heap → Prop) EPost⟨HeapException → Prop⟩ := StateT.instWPMonad
    intro heap hstar
    rw [StateT.apply_wp]
    simp only [wp]
    exact hstar
  wp_trans_bind x f := by
    intro post epost
    apply hForall_intro
    intro H
    apply hForall_elim H (Q := H -∗ _)
    apply hWand_mono
    letI : WPMonad HeapM (Heap → Prop) EPost⟨HeapException → Prop⟩ := StateT.instWPMonad
    apply PartialOrder.rel_trans
    · apply WPMonad.wp_consequence (m := HeapM) (x := x)
      intro a
      change H ∗ (∀ʰ K, K -∗ @wp HeapM _ _ _ _ _ StateT.instWPMonad _ (f a)
          (fun x => K ∗ post x) epost) ⊑
        @wp HeapM _ _ _ _ _ StateT.instWPMonad _ (f a) (fun x => H ∗ post x) epost
      exact hForall_star_elim H hWand_elim
    · exact WPMonad.wp_bind (m := HeapM) (x := x) (f := f)
        (post := fun x => H ∗ post x) epost
  wp_trans_monotone x := by
    intro post post' epost epost' hepost hpost
    apply hForall_intro
    intro H
    apply hForall_elim H (Q := H -∗ _)
    apply hWand_mono
    letI : WPMonad HeapM (Heap → Prop) EPost⟨HeapException → Prop⟩ := StateT.instWPMonad
    apply WPMonad.wp_consequence_econs (m := HeapM) (x := x)
    · intro a
      exact hStar_mono (hpost a)
    · exact hepost

def HeapM.frame (H pre : hProp) (post : α → hProp)
    (epost : EPost⟨HeapException → Prop⟩) (x : HeapM α) :
  Triple pre x post epost →
  Triple (H ∗ pre) x (fun x => H ∗ post x) epost := by
  intro hpre
  apply Triple.iff.mpr
  have hwp := Triple.iff.mp hpre
  unfold wp
  unfold wp at hwp
  unfold WPMonad.wpTrans
  unfold WPMonad.wpTrans at hwp
  simp only [HeapM.instWPMonadFrame]
  apply hForall_intro
  intro K
  apply entails_hWand
  letI : WPMonad HeapM (Heap → Prop) EPost⟨HeapException → Prop⟩ := StateT.instWPMonad
  have hwp' := PartialOrder.rel_trans hwp (hForall_elim (K ∗ H) PartialOrder.rel_refl)
  have step1 := PartialOrder.rel_trans (hStar_mono hwp') hWand_elim
  have step2 := WPMonad.wp_consequence (m := HeapM) (x := x)
    (fun a => (K ∗ H) ∗ post a) (fun a => K ∗ (H ∗ post a)) epost (fun _ => hStar_assoc_l)
  intro heap hKHpre
  exact step2 heap (step1 heap (hStar_assoc_r heap hKHpre))


theorem HeapM.read_spec (x : Loc) (v : Val) :
  ⦃ x ↦ v ⦄ read x ⦃ u, ⌜u = v⌝ʰ ∗ x ↦ v ⦄ := by
  simp [Triple.iff]
  apply hForall_intro
  intro H
  apply entails_hWand
  simp [← Triple.iff]
  letI : WPMonad HeapM (Heap → Prop) EPost⟨HeapException → Prop⟩ := StateT.instWPMonad
  exact read_inner x v H _


theorem HeapM.assign_spec (x : Loc) (v u : Val) :
  ⦃ x ↦ u ⦄ assign x v ⦃ _, x ↦ v ⦄ := by
  simp [Triple.iff]
  apply hForall_intro
  intro H
  apply entails_hWand
  simp [← Triple.iff]
  letI : WPMonad HeapM (Heap → Prop) EPost⟨HeapException → Prop⟩ := StateT.instWPMonad
  exact assign_inner x v u H _


theorem HeapM.alloc_spec (v : Val) :
  ⦃ ∅ ⦄ alloc v ⦃ x, x ↦ v ⦄ := by
  simp [Triple.iff]
  apply hForall_intro
  intro H
  apply entails_hWand
  simp [← Triple.iff]
  letI : WPMonad HeapM (Heap → Prop) EPost⟨HeapException → Prop⟩ := StateT.instWPMonad
  exact alloc_inner v H _
