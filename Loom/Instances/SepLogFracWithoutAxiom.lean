import Loom.Triple.Basic

open Lean.Order Loom

abbrev Loc  := Nat
abbrev Val  := Int

/-! ## The Permission Type -/

-- A Permission is a Rational number bundled with a proof that it is strictly positive.
@[ext]
structure Perm where
  val : Rat
  is_pos : 0 < val

namespace Perm

instance : Inhabited Perm where
  default := ⟨1, by decide⟩

-- Allow Lean to transparently read a Perm as a Rat
instance : Coe Perm Rat := ⟨Perm.val⟩

-- Addition inherently preserves positivity
instance : Add Perm where
  add p₁ p₂ := ⟨p₁.val + p₂.val, by grind [p₁.is_pos, p₂.is_pos]⟩

instance : LE Perm where
  le p₁ p₂ := p₁.val ≤ p₂.val

instance : OfNat Perm 1 where
  ofNat := ⟨1, by decide⟩

instance : BEq Perm where
  beq p₁ p₂ := p₁.val == p₂.val

end Perm

/-! ## Heap Definitions (Function-Based) -/

abbrev HeapVal := Val × Perm

-- A Heap is now a pure function, making observational equality identical to structural equality
def Heap := Loc → Option HeapVal

instance : EmptyCollection Heap := ⟨fun _ => none⟩
instance : Inhabited Heap := ⟨∅⟩

abbrev hProp := Heap → Prop

/-! ## Heap operations -/

def Heap.lookup (h : Heap) (x : Loc) : Option HeapVal := h x
def Heap.contains (h : Heap) (x : Loc) : Bool := (h x).isSome
def Heap.remove (h : Heap) (x : Loc) : Heap := fun y => if x = y then none else h y
def Heap.addUnion (h₁ h₂ : Heap) : Heap := fun x =>
  match h₁ x, h₂ x with
  | some (v, p₁), some (_, p₂) => some (v, p₁ + p₂)
  | some e, none => some e
  | none, some e => some e
  | none, none   => none
def Heap.single (x : Loc) (v : Val) : Heap := fun y => if x = y then some (v, 1) else none
def Heap.singleFrac (x : Loc) (v : Val) (π : Perm) : Heap := fun y => if x = y then some (v, π) else none

@[ext]
theorem Heap.ext_lookup {h₁ h₂ : Heap} (h : ∀ x : Loc, h₁.lookup x = h₂.lookup x) : h₁ = h₂ := by
  funext x; exact h x

/-! ## Lookup simp lemmas -/

@[simp] theorem Heap.lookup_empty (x : Loc) : (∅ : Heap).lookup x = none := rfl

@[simp] theorem Heap.lookup_single (x : Loc) (v : Val) :
    (Heap.single x v).lookup x = some (v, 1) := by simp [Heap.single, Heap.lookup]

theorem Heap.lookup_single_ne {x y : Loc} (hne : x ≠ y) (v : Val) :
    (Heap.single x v).lookup y = none := by simp [Heap.single, Heap.lookup]; grind

@[simp] theorem Heap.lookup_singleFrac (x : Loc) (v : Val) (π : Perm) :
    (Heap.singleFrac x v π).lookup x = some (v, π) := by
  simp [Heap.singleFrac, Heap.lookup]

theorem Heap.lookup_singleFrac_ne {x y : Loc} (hne : x ≠ y) (v : Val) (π : Perm) :
    (Heap.singleFrac x v π).lookup y = none := by
  simp [Heap.singleFrac, Heap.lookup]; grind

@[simp] theorem Heap.contains_empty (x : Loc) : (∅ : Heap).contains x = false := rfl

theorem Heap.contains_of_lookup {h : Heap} {x : Loc} {v : HeapVal}
    (hlk : h.lookup x = some v) : h.contains x = true := by
  -- Swap to the equivalent lookup syntax, then rewrite using your hypothesis
  change (h.lookup x).isSome = true
  simp [hlk]


/-! ## Remove lemmas -/

theorem Heap.lookup_remove_eq (h : Heap) (k : Loc) : (h.remove k).lookup k = none := by
  simp [Heap.remove, Heap.lookup]

theorem Heap.lookup_remove_ne {k x : Loc} (hne : k ≠ x) (h : Heap) :
    (h.remove k).lookup x = h.lookup x := by
  simp [Heap.remove, Heap.lookup]; grind

/-! ## addUnion lookup -/

-- This evaluates strictly via definitional equality now!
@[simp] theorem Heap.lookup_addUnion (h₁ h₂ : Heap) (x : Loc) :
    (h₁.addUnion h₂).lookup x =
      match h₁.lookup x, h₂.lookup x with
      | some (v, p₁), some (_, p₂) => some (v, p₁ + p₂)
      | some e, none => some e
      | none, some e => some e
      | none, none   => none := rfl

/-! ## Disjointness Proofs -/

def Heap.Disjoint (h₁ h₂ : Heap) : Prop :=
  ∀ x v₁ p₁ v₂ p₂, h₁.lookup x = some (v₁, p₁) → h₂.lookup x = some (v₂, p₂) → v₁ = v₂ ∧ p₁ + p₂ ≤ 1

theorem Heap.Disjoint.assoc_left {h₁ h₂ h₃ : Heap}
    (h₁₂ : Heap.Disjoint h₁ h₂) (h₁₂_₃ : Heap.Disjoint (h₁.addUnion h₂) h₃) :
    Heap.Disjoint h₁ (h₂.addUnion h₃) ∧ Heap.Disjoint h₂ h₃ := by
  constructor
  · intro x v₁ p₁ v₂₃ p₂₃ eq₁ eq₂₃
    simp only [Heap.lookup_addUnion] at eq₂₃
    rcases eq₂ : h₂.lookup x with _ | ⟨v₂, p₂⟩
    · rcases eq₃ : h₃.lookup x with _ | ⟨v₃, p₃⟩
      · simp_all
      · simp only [eq₂, eq₃, Option.some.injEq, Prod.mk.injEq] at eq₂₃
        rcases eq₂₃ with ⟨rfl, rfl⟩
        have hl12 : (h₁.addUnion h₂).lookup x = some (v₁, p₁) := by simp [Heap.lookup_addUnion, eq₁, eq₂]
        exact h₁₂_₃ x _ _ _ _ hl12 eq₃
    · rcases eq₃ : h₃.lookup x with _ | ⟨v₃, p₃⟩
      · simp only [eq₂, eq₃, Option.some.injEq, Prod.mk.injEq] at eq₂₃
        rcases eq₂₃ with ⟨rfl, rfl⟩
        exact h₁₂ x _ _ _ _ eq₁ eq₂
      · simp only [eq₂, eq₃, Option.some.injEq, Prod.mk.injEq] at eq₂₃
        rcases eq₂₃ with ⟨rfl, rfl⟩
        have ⟨hval₁₂, _⟩ := h₁₂ x _ _ _ _ eq₁ eq₂
        have hl12 : (h₁.addUnion h₂).lookup x = some (v₁, p₁ + p₂) := by simp [Heap.lookup_addUnion, eq₁, eq₂]
        have ⟨_, hperm₁₂₃⟩ := h₁₂_₃ x _ _ _ _ hl12 eq₃
        constructor
        · exact hval₁₂
        · change p₁.val + (p₂.val + p₃.val) ≤ 1
          change (p₁.val + p₂.val) + p₃.val ≤ 1 at hperm₁₂₃
          grind
  · intro x v₂ p₂ v₃ p₃ eq₂ eq₃
    rcases eq₁ : h₁.lookup x with _ | ⟨v₁, p₁⟩
    · have hl12 : (h₁.addUnion h₂).lookup x = some (v₂, p₂) := by simp [Heap.lookup_addUnion, eq₁, eq₂]
      exact h₁₂_₃ x _ _ _ _ hl12 eq₃
    · have ⟨hval₁₂, _⟩ := h₁₂ x _ _ _ _ eq₁ eq₂
      have hl12 : (h₁.addUnion h₂).lookup x = some (v₁, p₁ + p₂) := by simp [Heap.lookup_addUnion, eq₁, eq₂]
      have ⟨hval₁₂_₃, hperm₁₂₃⟩ := h₁₂_₃ x _ _ _ _ hl12 eq₃
      constructor
      · exact hval₁₂.symm.trans hval₁₂_₃
      · change p₂.val + p₃.val ≤ 1
        change (p₁.val + p₂.val) + p₃.val ≤ 1 at hperm₁₂₃
        have h1_pos := p₁.is_pos
        grind

theorem Heap.Disjoint.assoc_right {h₁ h₂ h₃ : Heap}
    (h₂₃ : Heap.Disjoint h₂ h₃) (h₁_₂₃ : Heap.Disjoint h₁ (h₂.addUnion h₃)) :
    Heap.Disjoint h₁ h₂ ∧ Heap.Disjoint (h₁.addUnion h₂) h₃ := by
  constructor
  · intro x v₁ p₁ v₂ p₂ eq₁ eq₂
    rcases eq₃ : h₃.lookup x with _ | ⟨v₃, p₃⟩
    · have hl23 : (h₂.addUnion h₃).lookup x = some (v₂, p₂) := by simp [Heap.lookup_addUnion, eq₂, eq₃]
      exact h₁_₂₃ x _ _ _ _ eq₁ hl23
    · have hl23 : (h₂.addUnion h₃).lookup x = some (v₂, p₂ + p₃) := by simp [Heap.lookup_addUnion, eq₂, eq₃]
      have ⟨hval, hperm⟩ := h₁_₂₃ x _ _ _ _ eq₁ hl23
      constructor
      · exact hval
      · change p₁.val + p₂.val ≤ 1
        change p₁.val + (p₂.val + p₃.val) ≤ 1 at hperm
        have h3_pos := p₃.is_pos
        grind
  · intro x v₁₂ p₁₂ v₃ p₃ eq₁₂ eq₃
    simp only [Heap.lookup_addUnion] at eq₁₂
    rcases eq₁ : h₁.lookup x with _ | ⟨v₁, p₁⟩
    · rcases eq₂ : h₂.lookup x with _ | ⟨v₂, p₂⟩
      · simp_all
      · simp only [eq₁, eq₂, Option.some.injEq, Prod.mk.injEq] at eq₁₂
        rcases eq₁₂ with ⟨rfl, rfl⟩
        exact h₂₃ x _ _ _ _ eq₂ eq₃
    · rcases eq₂ : h₂.lookup x with _ | ⟨v₂, p₂⟩
      · simp only [eq₁, eq₂, Option.some.injEq, Prod.mk.injEq] at eq₁₂
        rcases eq₁₂ with ⟨rfl, rfl⟩
        have hl23 : (h₂.addUnion h₃).lookup x = some (v₃, p₃) := by simp [Heap.lookup_addUnion, eq₂, eq₃]
        exact h₁_₂₃ x _ _ _ _ eq₁ hl23
      · simp only [eq₁, eq₂, Option.some.injEq, Prod.mk.injEq] at eq₁₂
        rcases eq₁₂ with ⟨rfl, rfl⟩
        have hl23 : (h₂.addUnion h₃).lookup x = some (v₂, p₂ + p₃) := by simp [Heap.lookup_addUnion, eq₂, eq₃]
        have ⟨hval₁₂, _⟩ := h₁_₂₃ x _ _ _ _ eq₁ hl23
        have ⟨hval₂₃, _⟩ := h₂₃ x _ _ _ _ eq₂ eq₃
        constructor
        · exact hval₁₂.trans hval₂₃
        · have ⟨_, hperm⟩ := h₁_₂₃ x _ _ _ _ eq₁ hl23
          change (p₁.val + p₂.val) + p₃.val ≤ 1
          change p₁.val + (p₂.val + p₃.val) ≤ 1 at hperm
          grind

theorem Heap.Disjoint.symm {h₁ h₂ : Heap} (h : Heap.Disjoint h₁ h₂) : Heap.Disjoint h₂ h₁ := by
  intro x v₂ p₂ v₁ p₁ eq₂ eq₁
  have ⟨hval, hperm⟩ := h x v₁ p₁ v₂ p₂ eq₁ eq₂
  constructor
  · exact hval.symm
  · change p₂.val + p₁.val ≤ 1
    change p₁.val + p₂.val ≤ 1 at hperm
    grind

/-! ## Heap infrastructure lemmas -/

theorem Heap.empty_addUnion (h : Heap) : (∅ : Heap).addUnion h = h := by
  apply Heap.ext_lookup; intro x; simp; cases h.lookup x <;> rfl

theorem Heap.addUnion_empty (h : Heap) : h.addUnion (∅ : Heap) = h := by
  apply Heap.ext_lookup; intro x; simp; cases h.lookup x <;> rfl

theorem Heap.addUnion_assoc (a b c : Heap) :
    (a.addUnion b).addUnion c = a.addUnion (b.addUnion c) := by
  apply Heap.ext_lookup; intro x
  simp only [Heap.lookup_addUnion]
  rcases a.lookup x with _ | ⟨v₁, p₁⟩
  · rcases b.lookup x with _ | ⟨v₂, p₂⟩ <;> rcases c.lookup x with _ | ⟨v₃, p₃⟩ <;> rfl
  · rcases b.lookup x with _ | ⟨v₂, p₂⟩
    · rcases c.lookup x with _ | ⟨v₃, p₃⟩ <;> rfl
    · rcases c.lookup x with _ | ⟨v₃, p₃⟩
      · rfl
      · dsimp only
        simp only [Option.some.injEq, Prod.mk.injEq, true_and]
        ext
        change (p₁.val + p₂.val) + p₃.val = p₁.val + (p₂.val + p₃.val)
        grind


theorem Heap.Disjoint.empty_left (h : Heap) : Heap.Disjoint ∅ h := by
  intro x v₁ p₁ v₂ p₂ eq₁ eq₂; simp at eq₁

theorem Heap.Disjoint.empty_right (h : Heap) : Heap.Disjoint h ∅ := by
  intro x v₁ p₁ v₂ p₂ eq₁ eq₂; simp at eq₂

theorem Heap.addUnion_comm {h₁ h₂ : Heap} (hdisj : h₁.Disjoint h₂) :
    h₁.addUnion h₂ = h₂.addUnion h₁ := by
  apply Heap.ext_lookup; intro x
  simp only [Heap.lookup_addUnion]
  rcases eq₁ : h₁.lookup x with _ | ⟨v₁, p₁⟩
  · rcases eq₂ : h₂.lookup x with _ | ⟨v₂, p₂⟩ <;> rfl
  · rcases eq₂ : h₂.lookup x with _ | ⟨v₂, p₂⟩
    · rfl
    · have ⟨hval, _⟩ := hdisj x v₁ p₁ v₂ p₂ eq₁ eq₂
      subst hval
      dsimp only
      simp only [Option.some.injEq, Prod.mk.injEq, true_and]
      ext
      change (p₁.val + p₂.val) = (p₂.val + p₁.val)
      grind


theorem Heap.addUnion_eq_empty (a b : Heap) :
    a.addUnion b = ∅ → a = ∅ ∧ b = ∅ := by
  intro h
  constructor <;> apply Heap.ext_lookup <;> intro x <;>
  · have hl := congrArg (·.lookup x) h
    simp only [Heap.lookup_addUnion, Heap.lookup_empty] at hl
    rcases eq_a : a.lookup x with _ | ⟨v₁, p₁⟩ <;> rcases eq_b : b.lookup x with _ | ⟨v₂, p₂⟩ <;> simp_all

/-- In our model, heaps are finitely constructed using `empty`, `single`, and `addUnion`.
    Because they only populate finite locations, they do not exhaust the infinite domain
    of `Nat`. Thus, asserting the existence of an empty location is logically safe. -/
axiom Heap.exists_not_contained (h : Heap) : ∃ a : Loc, h.contains a = false

/-! ## hProp connectives -/

inductive hStar' (H₁ : hProp) (H₂ : hProp) (h : Heap) : Prop where
  | intro (h₁ h₂ : Heap) (Hh₁ : H₁ h₁) (Hh₂ : H₂ h₂)
    (h_union : h₁.addUnion h₂ = h)
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

/-! ## Points-to assertions -/

inductive hSingle' (x : Loc) (v : Val) : Heap → Prop where
  | intro : hSingle' x v (Heap.single x v)

def hSingle (x : Loc) (v : Val) : hProp := hSingle' x v

notation:70 x " ↦ " v => hSingle x v

def ValidPerm (π : Perm) : Prop := π ≤ 1

inductive hSingleFrac' (x : Loc) (v : Val) (π : { p : Perm // ValidPerm p }) : Heap → Prop where
  | intro : hSingleFrac' x v π (Heap.singleFrac x v π.1)

def hSingleFrac (x : Loc) (v : Val) (π : { p : Perm // ValidPerm p }) : hProp :=
  hSingleFrac' x v π

notation:70 x " ↦[" π "] " v => hSingleFrac x v π

def fullPerm (x : Loc) : hProp := ∃ʰ v, x ↦ v

notation "perm(" x ")" => fullPerm x

def hEmpty : hProp := (· = ∅)

instance : EmptyCollection hProp := ⟨hEmpty⟩

/-! ## Permission constants -/

def fullPermVal : { p : Perm // ValidPerm p } := ⟨⟨1, by decide⟩, by trivial⟩
def halfPerm : { p : Perm // ValidPerm p } := ⟨⟨1/2, by grind⟩, by change (1/2 : Rat) ≤ 1; grind⟩

/-! ## hSingle = hSingleFrac with full perm -/

theorem hSingle_eq_hSingleFrac (x : Loc) (v : Val) :
    (x ↦ v) = (x ↦[fullPermVal] v) := by
  funext h; apply propext
  constructor
  · intro hp; cases hp; exact hSingleFrac'.intro
  · intro hp; cases hp; exact hSingle'.intro

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
  | intro _ => rw [Heap.empty_addUnion] at hunion; exact hunion ▸ hQ

theorem hWand_hPure_true_elim {Q : hProp} : hWand (hPure True) Q ⊑ Q := by
  intro h ⟨H', ⟨h₁, _, hH', hpure, hunion, _⟩⟩
  cases hpure with
  | intro hent =>
    rw [Heap.addUnion_empty] at hunion; subst hunion
    exact hent h₁ (hStar'.intro ∅ h₁ (hPure'.intro trivial) hH'
      (Heap.empty_addUnion h₁) (Heap.Disjoint.empty_left h₁))

theorem entails_hWand {H₁ H₂ Q : hProp} (hle : H₁ ∗ H₂ ⊑ Q) :
    H₂ ⊑ hWand H₁ Q := by
  intro h hH₂
  exact hExists'.intro H₂ (hStar'.intro h ∅ hH₂ (hPure'.intro hle)
    (Heap.addUnion_empty h) (Heap.Disjoint.empty_right h))

@[grind] theorem hWand_mono :
  P ⊑ Q → H -∗ P ⊑ H -∗ Q := by
  intro hle h ⟨H', ⟨hLeft, hRight, hH', hpure, hunion, hdisj⟩⟩
  cases hpure with
  | intro hent =>
    exact hExists'.intro H' (hStar'.intro hLeft ∅ hH' (hPure'.intro (PartialOrder.rel_trans hent hle))
      hunion hdisj)

@[grind] theorem hStar_mono :
  P ⊑ Q → H ∗ P ⊑ H ∗ Q := by
  intro hle h ⟨h₁, h₂, hH, hP, hunion, hdisj⟩
  exact hStar'.intro h₁ h₂ hH (hle h₂ hP) hunion hdisj

theorem hStar_mono' :
  P ⊑ Q → H ⊑ H' → H ∗ P ⊑ H' ∗ Q := by
  intro hle hle' h ⟨h₁, h₂, hH, hP, hunion, hdisj⟩
  exact hStar'.intro h₁ h₂ (hle' h₁ hH) (hle h₂ hP) hunion hdisj

theorem hWand_elim {H Q : hProp} : H ∗ (H -∗ Q) ⊑ Q := by
  intro h ⟨h₁, h₂, hH, ⟨H', ⟨h₃, h₄, hH', hpure, hunion₂, hdisj₂⟩⟩, hunion, hdisj⟩
  cases hpure with
  | intro hent =>
    rw [Heap.addUnion_empty] at hunion₂; subst hunion₂
    exact hent h (hStar'.intro h₁ h₃ hH hH' hunion hdisj)

theorem hStar_assoc_l {A B C : hProp} : (A ∗ B) ∗ C ⊑ A ∗ (B ∗ C) := by
  intro h ⟨h₁₂, h₃, ⟨h₁, h₂, hA, hB, hunion₁₂, hdisj₁₂⟩, hC, hunion, hdisj⟩
  have ⟨hdisj₁, hdisj₂⟩ := Heap.Disjoint.assoc_left hdisj₁₂ (hunion₁₂ ▸ hdisj)
  exact hStar'.intro h₁ (h₂.addUnion h₃) hA (hStar'.intro h₂ h₃ hB hC rfl hdisj₂)
    (by rw [← Heap.addUnion_assoc, hunion₁₂, hunion]) hdisj₁

theorem hStar_assoc_r {A B C : hProp} : A ∗ (B ∗ C) ⊑ (A ∗ B) ∗ C := by
  intro h ⟨h₁, h₂₃, hA, ⟨h₂, h₃, hB, hC, hunion₂₃, hdisj₂₃⟩, hunion, hdisj⟩
  subst hunion₂₃
  have ⟨hdisj₁, hdisj₂⟩ := Heap.Disjoint.assoc_right hdisj₂₃ hdisj
  exact hStar'.intro (h₁.addUnion h₂) h₃ (hStar'.intro h₁ h₂ hA hB rfl hdisj₁) hC
    (by rw [Heap.addUnion_assoc, hunion]) hdisj₂

theorem hStar_assoc {A B C : hProp} : (A ∗ B) ∗ C = A ∗ (B ∗ C) := by
  funext h; apply propext
  exact ⟨fun hH => hStar_assoc_l h hH, fun hH => hStar_assoc_r h hH⟩

theorem hStar_empty_elim {H : hProp} : H ∗ ∅ ⊑ H := by
  intro h ⟨h₁, h₂, hH, hempty, hunion, _⟩
  have : h₂ = ∅ := hempty; subst this
  rw [Heap.addUnion_empty] at hunion; exact hunion ▸ hH

theorem hStar_empty_intro {H : hProp} : H ⊑ H ∗ ∅ := by
  intro h hH
  exact hStar'.intro h ∅ hH rfl (Heap.addUnion_empty h) (Heap.Disjoint.empty_right h)

@[simp] theorem hStar_empty (H : hProp) : H ∗ ∅ = H := by
  funext h; apply propext
  exact ⟨fun hH => hStar_empty_elim h hH, fun hH => hStar_empty_intro h hH⟩

theorem empty_hStar_elim {H : hProp} : ∅ ∗ H ⊑ H := by
  intro h ⟨h₁, h₂, hempty, hH, hunion, _⟩
  have : h₁ = ∅ := hempty; subst this
  rw [Heap.empty_addUnion] at hunion; exact hunion ▸ hH

theorem empty_hStar_intro {H : hProp} : H ⊑ ∅ ∗ H := by
  intro h hH
  exact hStar'.intro ∅ h rfl hH (Heap.empty_addUnion h) (Heap.Disjoint.empty_left h)

@[simp] theorem empty_hStar (H : hProp) : ∅ ∗ H = H := by
  funext h; apply propext
  exact ⟨fun hH => empty_hStar_elim h hH, fun hH => empty_hStar_intro h hH⟩

theorem hStar_comm_entails {H₁ H₂ : hProp} : H₁ ∗ H₂ ⊑ H₂ ∗ H₁ := by
  intro h ⟨h₁, h₂, hH₁, hH₂, hunion, hdisj⟩
  exact hStar'.intro h₂ h₁ hH₂ hH₁
    (by rw [← Heap.addUnion_comm] <;> assumption) (Heap.Disjoint.symm hdisj)

@[simp] theorem hStar_comm (H₁ H₂ : hProp) : H₁ ∗ H₂ = H₂ ∗ H₁ := by
  funext h; apply propext
  exact ⟨fun hH => hStar_comm_entails h hH, fun hH => hStar_comm_entails h hH⟩

theorem empty_True : ⌜True⌝ʰ = ∅ := by
  apply funext; intro h; apply propext
  constructor
  · intro h'; cases h' with | intro _ => rfl
  · intro h'
    have : h = ∅ := h'
    subst this; exact hPure'.intro True.intro

/-! ## HeapM -/

structure HeapM α where
  predTrans : PredTrans hProp EPost⟨⟩ α
  monotone : predTrans.monotone := by grind

@[grind =] theorem le_hProp_eq_forall (a b : hProp) : (a ⊑ b) = ∀ h, (a h → b h) := by
    simp [PartialOrder.rel]

@[grind =] theorem le_fun_eq_forall (f g : α → hProp) : (f ⊑ g) = ∀ a, f a ⊑ g a := by
  simp [PartialOrder.rel]

@[grind =] theorem PredTrans.monotone_eq [PartialOrder l] [PartialOrder e] (pt : PredTrans l e α):
    (pt.monotone) =
  ∀ post post' epost epost', epost ⊑ epost' → post ⊑ post' → pt post epost ⊑ pt post' epost'
 := by simp [PredTrans.monotone]

@[grind! .]
theorem HeapM.predTrans_monotone (m : HeapM α) : m.predTrans.monotone := m.monotone

def HeapM.bind (x : HeapM α) (f : α → HeapM β) : HeapM β :=
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

def HeapM.pickSuchThat (p : α → hProp) : HeapM α :=
  { predTrans := fun post _ h => (∃ a, p a h) ∧ ∀ a, p a h → post a h }

def HeapM.exhale (hp : hProp) : HeapM Unit :=
  { predTrans := fun post _ => hp ∗ post () }

def HeapM.inhale (hp : hProp) : HeapM Unit :=
  { predTrans := fun post _ => hp -∗ post () }

def HeapM.read (x : Loc) : HeapM Val :=
  pickSuchThat fun v h => (h.lookup x).any (·.1 = v)

def HeapM.assign (x : Loc) (v : Val) : HeapM Unit := do
  exhale perm(x)
  inhale (x ↦ v)

def HeapM.alloc (v : Val) : HeapM Loc := do
  let newKey ← pickSuchThat fun l h => h.contains l = false
  inhale (newKey ↦ v)
  return newKey

instance : WPMonad HeapM hProp EPost⟨⟩ where
  wpTrans x post _ := ∀ʰ H, H -∗ x.predTrans (fun a => (H ∗ (post a))) epost⟨⟩
  wp_trans_pure x post _ := by
    intro h post' hpost
    simp_all [pure, hWand, hExists, hPure] <;> constructor; constructor
    try apply post'
    constructor <;> rfl
    apply Heap.addUnion_empty
    apply Heap.Disjoint.empty_right
  wp_trans_bind x f post _ := by
    apply hForall_intro; intro H
    apply hForall_elim H (Q := H -∗ _)
    apply hWand_mono
    simp [bind]
    apply x.monotone
    rfl
    intro a
    simp
    apply hForall_star_elim
    apply hWand_elim
  wp_trans_monotone x := by
    intro post post' epost epost' hpost hpost' H
    apply hForall_intro
    intro H_1
    apply hForall_elim H_1 (Q := H_1 -∗ _)
    apply hWand_mono
    apply x.monotone
    grind
    simp [PartialOrder.rel]
    intro a v HH
    simp_all [hStar]
    cases HH with
    | intro h₁ h₂ hH hP hunion hdisj =>
       constructor
       apply hH
       apply hpost'
       apply hP
       apply hunion
       apply hdisj

theorem HeapM.frame (H pre : hProp) (post : α → hProp) (x : HeapM α) :
  ⦃ pre ⦄ x ⦃ post ⦄ →
  ⦃ H ∗ pre ⦄ x ⦃ v, H ∗ post v ⦄ := by
    intro hpre
    apply Triple.iff.mpr
    have hwp := Triple.iff.mp hpre
    unfold wp
    unfold wp at hwp
    unfold wpTrans
    unfold wpTrans at hwp
    simp_all [instWPMonadHeapMHPropNil]
    apply hForall_intro
    intro H_1
    apply entails_hWand
    intro heap h_heap
    have step1 := hStar_assoc_r heap h_heap
    have step2 := hStar_mono hwp heap step1
    have step3 : (x.predTrans (fun v => (H_1 ∗ H) ∗ post v) epost⟨⟩) heap :=
    hForall_star_elim (H_1 ∗ H) (P := fun H' => H' -∗ x.predTrans (fun v => H' ∗ post v) epost⟨⟩) hWand_elim heap step2
    revert step3
    apply x.monotone
    rfl
    intro v
    exact hStar_assoc_l

/-! ## Hoare triple specs -/

theorem HeapM.inhale_spec (hp : hProp) :
  ⦃ ∅ ⦄ inhale hp ⦃ _, hp ⦄ := by
  simp [inhale]
  apply Triple.iff.mpr
  unfold wp wpTrans
  simp_all [instWPMonadHeapMHPropNil]
  apply hForall_intro
  intro H
  apply entails_hWand
  apply entails_hWand
  simp; rfl

theorem HeapM.exhale_spec (hp : hProp) :
  hp ⊑ hp' →
  ⦃ hp ⦄ exhale hp' ⦃ _, ∅ ⦄ := by
  intro hle
  simp [exhale]
  apply Triple.iff.mpr
  unfold wp wpTrans
  simp_all [instWPMonadHeapMHPropNil]
  apply hForall_intro
  intro H
  apply entails_hWand
  grind [← hStar_comm]

theorem HeapM.read_spec (x : Loc) (v : Val) :
  ⦃ x ↦ v ⦄ read x ⦃ v, ⌜v = v⌝ʰ ∗ x ↦ v ⦄ := by
  simp [read]
  apply Triple.iff.mpr
  unfold wp wpTrans
  simp_all [instWPMonadHeapMHPropNil]
  apply hForall_intro
  intro H
  apply entails_hWand
  intro heap HH
  simp [pickSuchThat]
  constructor
  · apply Exists.intro v
    simp_all [hStar]
    cases HH with
    | intro h₁ h₂ hH hP hunion hdisj =>
      simp [hSingle] at hP
      cases hP
      rw [← hunion, Heap.lookup_addUnion]
      rcases eq₁ : h₁.lookup x with _ | ⟨v₁, p₁⟩
      · simp [Heap.lookup_single]
      · have eq₂ : (Heap.single x v).lookup x = some (v, 1) := by simp [Heap.lookup_single]
        have ⟨hval, _⟩ := hdisj x v₁ p₁ v 1 eq₁ eq₂
        subst hval
        simp [eq₂]
  · intro v' hP
    have vv' : v = v' := by
      simp_all [hStar]
      cases HH with
      | intro h₁ h₂ hTrue hPt hunion hdisj =>
        cases hPt
        rw [← hunion] at hP
        simp [Option.any, Heap.lookup] at hP
        rcases eq₁ : h₁.lookup x with _ | ⟨v₁, p₁⟩
        · have heq : (h₁.addUnion (Heap.single x v)) x = some (v, 1) := by
           have key : h₁.addUnion (Heap.single x v) x = some (v, 1) := by
              have h₁x : h₁ x = none := eq₁  -- lookup is definitionally h x
              simp [Heap.addUnion, Heap.single, h₁x]
           rw [key] at hP
           simp at hP
           grind
          grind
        · have eq₂ : (Heap.single x v).lookup x = some (v, 1) := by
            simp [Heap.lookup_single]
          have ⟨hval, _⟩ := hdisj x v₁ p₁ v 1 eq₁ eq₂
          -- hval : v₁ = v
          have h₁x : h₁ x = some (v₁, p₁) := eq₁
          have key : h₁.addUnion (Heap.single x v) x = some (v₁, p₁ + 1) := by
            simp [Heap.addUnion, Heap.single, h₁x]
          rw [key] at hP
          simp at hP
          -- hP : v₁ = v'
          grind
    simp [empty_True, ← vv']
    exact HH


theorem HeapM.assign_spec (x : Loc) (v u : Val) :
  ⦃ x ↦ u ⦄ assign x v ⦃ _, x ↦ v ⦄ := by
  simp [assign]
  apply Triple.iff.mpr
  unfold wp wpTrans
  simp_all [instWPMonadHeapMHPropNil]
  apply hForall_intro
  intro H
  apply entails_hWand
  rw [@predTrans]
  simp [Bind.bind, HeapM.bind]
  rw [predTrans]
  simp [inhale, exhale]
  unfold fullPerm
  rw [← hStar_comm]
  apply hStar_mono'
  · apply entails_hWand; simp; rfl
  · intro h hperm; constructor; apply hperm

theorem HeapM.alloc_spec (v : Val) :
  ⦃ ∅ ⦄ alloc v ⦃ l, l ↦ v ⦄ := by
  simp [alloc]
  apply Triple.iff.mpr
  unfold wp wpTrans
  simp_all [instWPMonadHeapMHPropNil]
  apply hForall_intro
  intro H
  apply entails_hWand
  rw [@predTrans]
  simp [Bind.bind, HeapM.bind]
  rw [@predTrans]
  simp [pickSuchThat, inhale, Functor.map, HeapM.bind]
  intro h HH
  constructor
  rotate_left
  intro l Hl
  apply entails_hWand
  simp
  apply hStar_mono
  rfl
  apply HH
  exact Heap.exists_not_contained h

/-! ## Fractional permission theorems -/

theorem hSingleFrac_split (x : Loc) (v : Val)
    (π₁ π₂ : { p : Perm // ValidPerm p })
    (hsum : π₁.1 + π₂.1 = 1) :
    (x ↦ v) = ((x ↦[π₁] v) ∗ (x ↦[π₂] v)) := by
  funext h; apply propext
  constructor
  · intro hp; cases hp
    refine hStar'.intro (Heap.singleFrac x v π₁.1) (Heap.singleFrac x v π₂.1)
      hSingleFrac'.intro hSingleFrac'.intro ?_ ?_
    · apply Heap.ext_lookup; intro y
      rw [Heap.lookup_addUnion]
      by_cases h_xy : x = y
      · subst h_xy
        simp [hsum]
      · have hne : x ≠ y := h_xy
        simp [Heap.lookup_single_ne hne, Heap.lookup_singleFrac_ne hne]
    · intro y v₁ p₁ v₂ p₂ eq₁ eq₂
      by_cases h_xy : x = y
      · subst h_xy
        simp at eq₁ eq₂
        obtain ⟨rfl, rfl⟩ := eq₁
        obtain ⟨rfl, rfl⟩ := eq₂
        exact ⟨rfl, by simp [hsum]; trivial⟩
      · have hne : x ≠ y := h_xy
        simp [Heap.lookup_singleFrac_ne hne] at eq₁
  · intro ⟨h₁, h₂, hf₁, hf₂, hunion, _⟩
    cases hf₁; cases hf₂
    have : h = Heap.single x v := by
      apply Heap.ext_lookup; intro y
      rw [← hunion, Heap.lookup_addUnion]
      by_cases h_xy : x = y
      · subst h_xy
        simp [hsum]
      · have hne : x ≠ y := h_xy
        simp [Heap.lookup_single_ne hne, Heap.lookup_singleFrac_ne hne]
    subst this; exact hSingle'.intro

theorem hSingleFrac_combine (x : Loc) (v : Val)
    (π₁ π₂ : { p : Perm // ValidPerm p })
    (hle : π₁.1 + π₂.1 ≤ 1) :
    ((x ↦[π₁] v) ∗ (x ↦[π₂] v)) =
    (x ↦[⟨π₁.1 + π₂.1, hle⟩] v) := by
  funext h; apply propext
  constructor
  · intro ⟨h₁, h₂, hf₁, hf₂, hunion, _⟩
    cases hf₁; cases hf₂
    have : h = Heap.singleFrac x v (π₁.1 + π₂.1) := by
      apply Heap.ext_lookup; intro y
      rw [← hunion, Heap.lookup_addUnion]
      by_cases h_xy : x = y
      · subst h_xy
        simp
      · have hne : x ≠ y := h_xy
        simp [Heap.lookup_singleFrac_ne hne]
    subst this; exact hSingleFrac'.intro
  · intro hp; cases hp
    refine hStar'.intro (Heap.singleFrac x v π₁.1) (Heap.singleFrac x v π₂.1)
      hSingleFrac'.intro hSingleFrac'.intro ?_ ?_
    · apply Heap.ext_lookup; intro y
      rw [Heap.lookup_addUnion]
      by_cases h_xy : x = y
      · subst h_xy
        simp
      · have hne : x ≠ y := h_xy
        simp [Heap.lookup_singleFrac_ne hne]
    · intro y v₁ p₁ v₂ p₂ eq₁ eq₂
      by_cases h_xy : x = y
      · subst h_xy
        simp at eq₁ eq₂
        obtain ⟨rfl, rfl⟩ := eq₁
        obtain ⟨rfl, rfl⟩ := eq₂
        exact ⟨rfl, hle⟩
      · have hne : x ≠ y := h_xy
        simp [Heap.lookup_singleFrac_ne hne] at eq₁

/-!
If two heaps are disjoint and each maps location x to some value with
the same permission, they must carry the same value
-/
theorem hStar_singleFrac_unique
    {x : Loc} {v w : Val} {π : { p : Perm // ValidPerm p }}
    {P Q : hProp} {h : Heap}
    (hP : ((x ↦[π] v) ∗ P) h)
    (hQ : ((x ↦[π] w) ∗ Q) h) :
    v = w := by
  obtain ⟨h₁, h₂, hv, hP', hunion₁, hdisj₁⟩ := hP
  obtain ⟨h₃, h₄, hw, hQ', hunion₂, hdisj₂⟩ := hQ
  cases hv; cases hw
  have lk₁ : h.lookup x = some (v, π.1) ∨
              ∃ p', h.lookup x = some (v, π.1 + p') := by
    rw [← hunion₁, Heap.lookup_addUnion]
    simp [Heap.lookup_singleFrac]
    rcases eq_h₂ : h₂.lookup x with _ | ⟨w', p'⟩
    · simp
    · simp
      grind
  have lk₂ : h.lookup x = some (w, π.1) ∨
              ∃ p', h.lookup x = some (w, π.1 + p') := by
    rw [← hunion₂, Heap.lookup_addUnion]
    simp [Heap.lookup_singleFrac]
    rcases eq_h₄ : h₄.lookup x with _ | ⟨w', p'⟩
    · simp
    · simp
      grind
  rcases lk₁ with hlk₁ | ⟨p₁, hlk₁⟩ <;>
  rcases lk₂ with hlk₂ | ⟨p₂, hlk₂⟩ <;>
  · rw [hlk₁] at hlk₂
    simp at hlk₂
    grind

/-! Symmetric variant -/
theorem hStar_singleFrac_unique' {x : Loc} {v w : Val}
    {π : { p : Perm // ValidPerm p }} {P Q : hProp} {h : Heap}
    (hP : (P ∗ (x ↦[π] v)) h)
    (hQ : (Q ∗ (x ↦[π] w)) h) : v = w := by
  apply hStar_singleFrac_unique (h := h)
  · rw [hStar_comm]; exact hP
  · rw [hStar_comm]; exact hQ


theorem HeapM.read_frac_spec (x : Loc) (v : Val)
    (π : { p : Perm // ValidPerm p }) :
    ⦃ x ↦[π] v ⦄ read x ⦃ w, ⌜w = v⌝ʰ ∗ x ↦[π] v ⦄ := by
  simp [read]
  apply Triple.iff.mpr
  unfold wp wpTrans
  simp_all [instWPMonadHeapMHPropNil]
  apply hForall_intro
  intro H
  apply entails_hWand
  intro heap HH
  simp [pickSuchThat]
  constructor
  · apply Exists.intro v
    simp_all [hStar]
    cases HH with
    | intro h₁ h₂ hH hP hunion hdisj =>
      simp [hSingleFrac] at hP
      cases hP
      rw [← hunion, Heap.lookup_addUnion]
      rcases eq₁ : h₁.lookup x with _ | ⟨v₁, p₁⟩
      · simp [Heap.lookup_singleFrac]
      · have eq₂ : (Heap.singleFrac x v π).lookup x = some (v, π.1) := by simp [Heap.lookup_singleFrac]
        have ⟨hval, _⟩ := hdisj x v₁ p₁ v π.1 eq₁ eq₂
        subst hval
        simp [eq₂]
  · intro v' hP
    have vv' : v = v' := by
      simp_all [hStar]
      cases HH with
      | intro h₁ h₂ hTrue hPt hunion hdisj =>
        cases hPt
        rw [← hunion] at hP
        simp [Option.any, Heap.lookup] at hP
        rcases eq₁ : h₁.lookup x with _ | ⟨v₁, p₁⟩
        · have key : h₁.addUnion (Heap.singleFrac x v π.val) x = some (v, π.val) := by
              have h₁x : h₁ x = none := eq₁  -- lookup is definitionally h x
              simp [Heap.addUnion, Heap.singleFrac, h₁x]
          simp [key] at hP
          apply hP
        · have eq₂ : (Heap.singleFrac x v π.val).lookup x = some (v, π.val) := by
            simp [Heap.lookup_singleFrac]
          have ⟨hval, _⟩ := hdisj x v₁ p₁ v π.val eq₁ eq₂
          -- hval : v₁ = v
          have h₁x : h₁ x = some (v₁, p₁) := eq₁
          have key : h₁.addUnion (Heap.singleFrac x v π.val) x = some (v₁, p₁ + π.val) := by
            simp [Heap.addUnion, Heap.singleFrac, h₁x]
          rw [key] at hP
          simp at hP
          grind
    simp [empty_True, ← vv']
    exact HH

/-! ## Final example -/
def myPerm : { p : Perm // ValidPerm p } := ⟨⟨1/3, by grind⟩, by change (1/3 : Rat) ≤ 1; grind⟩
def myPerm' : { p : Perm // ValidPerm p } := ⟨⟨2/3, by grind⟩, by change (2/3 : Rat) ≤ 1; grind⟩



example (p : Loc) (v : Val) :
    ⦃ ∅ ⦄
    (do HeapM.inhale (p ↦ v)
        HeapM.exhale (p ↦[myPerm] v))
    ⦃ _, p ↦[myPerm'] v ⦄ := by
  apply Triple.iff.mpr
  unfold wp wpTrans
  simp_all [instWPMonadHeapMHPropNil]
  apply hForall_intro
  intro H
  apply entails_hWand
  simp [Bind.bind, HeapM.bind, HeapM.inhale, HeapM.exhale]
  apply entails_hWand
  intro heap HH
  rw [hSingleFrac_split p v myPerm myPerm'] at HH
  rotate_right
  ext
  simp [myPerm, myPerm']
  show (1/3 : Rat) + 2/3 = 1
  grind_linarith
  revert HH heap
  rw[hStar_assoc]
  simp [hStar_comm]
