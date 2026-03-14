import Std.Data.HashMap.Lemmas
import Loom.Triple.Basic

open Lean.Order Loom

abbrev Loc  := Nat
abbrev Val  := Int
abbrev Perm := Rat

instance : EquivBEq Loc := inferInstance
instance : LawfulHashable Loc := inferInstance

abbrev HeapVal := Val × { x : Perm // x > 0 ∧ x <= 1 }

abbrev Heap := Std.HashMap Loc HeapVal

instance : EmptyCollection Heap := inferInstance

abbrev hProp := Heap → Prop

def Heap.Disjoint (h₁ h₂ : Heap) : Prop :=
  ∀ x, h₁.contains x → h₂.contains x → False

private def fullPermVal : { x : Perm // x > 0 ∧ x <= 1 } := by
  refine ⟨1, ?_⟩
  decide

def Heap.single (x : Loc) (v : Val) : Heap := (∅ : Heap).insert x (v, fullPermVal)

-- `Std.HashMap` equality is representation-sensitive; separation-logic proofs
-- use this extensional principle over `get?`.
axiom Heap.ext_getElem? {h₁ h₂ : Heap} :
    (∀ x : Loc, h₁[x]? = h₂[x]?) → h₁ = h₂

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
  | intro : hSingle' x v (Heap.single x v)

def hSingle (x : Loc) (v : Val) : hProp := hSingle' x v

notation:70 x " ↦ " v => hSingle x v

def fullPerm (x : Loc) : hProp := ∃ʰ v, x ↦ v

notation "perm(" x ")" => fullPerm x

def hEmpty : hProp := (· = ∅)

instance : EmptyCollection hProp := ⟨hEmpty⟩

theorem Heap.empty_union (h : Heap) : (∅ : Heap).union h = h := by
  apply Heap.ext_getElem?
  intro x
  simp [Std.HashMap.getElem?_union]

theorem Heap.union_empty (h : Heap) : h.union (∅ : Heap) = h := by
  apply Heap.ext_getElem?
  intro x
  simp [Std.HashMap.getElem?_union]

theorem Heap.Disjoint.empty_left (h : Heap) : Heap.Disjoint ∅ h := by
  intro _ hx _
  exact absurd hx Std.HashMap.not_mem_empty

theorem Heap.Disjoint.empty_right (h : Heap) : Heap.Disjoint h ∅ := by
  intro _ _ hy
  exact absurd hy Std.HashMap.not_mem_empty


theorem Heap.union_eq_empty (a b : Heap) : (a.union b) = ∅ -> a = ∅ /\ b = ∅ := by
  intro _
  constructor
  · apply Heap.ext_getElem?
    intro x
    have hx : (a.union b)[x]? = (∅ : Heap)[x]? := by grind
    revert hx
    simp [Std.HashMap.getElem?_union]
  · apply Heap.ext_getElem?
    intro x
    have hx : (a.union b)[x]? = (∅ : Heap)[x]? := by grind
    revert hx
    simp [Std.HashMap.getElem?_union]
    grind



theorem Heap.union_assoc (a b c : Heap) : (a.union b).union c = a.union (b.union c) := by
  apply Heap.ext_getElem?
  intro x
  simp [Std.HashMap.getElem?_union, Option.or_assoc]

theorem Heap.Disjoint.assoc_left {h₁ h₂ h₃ : Heap}
    (h₁₂ : Heap.Disjoint h₁ h₂) (h₁₂_₃ : Heap.Disjoint (h₁.union h₂) h₃) :
    Heap.Disjoint h₁ (h₂.union h₃) ∧ Heap.Disjoint h₂ h₃ := by
  constructor
  · intro x hx hy
    have hy' : (h₂.contains x || h₃.contains x) = true := by
      simpa [Std.HashMap.contains_union] using hy
    simp only [Bool.or_eq_true] at hy'
    cases hy' with
    | inl h₂x => exact h₁₂ x hx h₂x
    | inr h₃x =>
      exact h₁₂_₃ x (by simp [Std.HashMap.contains_union, hx]) h₃x
  · intro x hx hy
    exact h₁₂_₃ x (by simp [Std.HashMap.contains_union, hx]) hy

theorem Heap.Disjoint.assoc_right {h₁ h₂ h₃ : Heap}
    (h₁_₂₃ : Heap.Disjoint h₁ (h₂.union h₃)) (h₂₃ : Heap.Disjoint h₂ h₃) :
    Heap.Disjoint h₁ h₂ ∧ Heap.Disjoint (h₁.union h₂) h₃ := by
  constructor
  · intro x hx hy
    exact h₁_₂₃ x hx (by simp [Std.HashMap.contains_union, hy])
  · intro x hx hy
    have hx' : (h₁.contains x || h₂.contains x) = true := by
      simpa [Std.HashMap.contains_union] using hx
    simp only [Bool.or_eq_true] at hx'
    cases hx' with
    | inl h₁x =>
      exact h₁_₂₃ x h₁x (by simp [Std.HashMap.contains_union, hy])
    | inr h₂x => exact h₂₃ x h₂x hy

/-! ## Abstract lemmas about hProp connectives -/

theorem hForall_elim {P : α → hProp} (a : α) :
  P a ⊑ Q →
  hForall P ⊑ Q :=
  fun himp _ hall =>
    himp _ (hall a)

theorem hForall_star_elim {P : α → hProp} (a : α) :
  H ∗ P a ⊑ Q →
  H ∗ hForall P ⊑ Q := by
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

@[grind] theorem hWand_mono :
  P ⊑ Q →
  H -∗ P ⊑ H -∗ Q := by
  intro hle h ⟨H', ⟨hLeft, hRight, hH', hpure, hunion, hdisj⟩⟩
  cases hpure with
  | intro hent =>
    exact hExists'.intro H' (hStar'.intro hLeft ∅ hH' (hPure'.intro (PartialOrder.rel_trans hent hle))
      hunion hdisj)

@[grind] theorem hStar_mono :
  P ⊑ Q →
  H ∗ P ⊑ H ∗ Q := by
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

abbrev HeapM α := { x : PredTrans hProp EPost⟨⟩ α // x.monotone }
/-
structure HeapM α where
  predTrans : PredTrans hProp EPost⟨⟩ α
  monotone : val.monotone := by grind
-/


@[grind =] theorem hh (a b : hProp) : (a ⊑ b) = ∀ h, (a h -> b h) := by
    simp[PartialOrder.rel]

@[grind =] theorem hh_fun (f g : α → hProp) : (f ⊑ g) = ∀ a, f a ⊑ g a := by
  simp [PartialOrder.rel]

@[grind =] theorem hh2 [PartialOrder l] [PartialOrder e] (pt : PredTrans l e α):
    (pt.monotone) =
  ∀ post post' epost epost', epost ⊑ epost' → post ⊑ post' → pt post epost ⊑ pt post' epost'
 := by simp [PredTrans.monotone]




def HeapM.bind (x : HeapM α) (f : α → HeapM β) : HeapM β :=
  ⟨fun post epost => x.val (fun a => (f a).val post epost) epost,
  by grind⟩

instance : Monad HeapM where
  pure a := ⟨fun post _ => post a, by simp [PredTrans.monotone, PartialOrder.rel]; grind⟩
  bind := HeapM.bind


instance  : LawfulMonad (HeapM) where
  map_const := rfl
  id_map _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := rfl

def HeapM.pickSuchThat (p : α -> hProp) : HeapM α := ⟨fun post _ h =>
  (∃ a, p a h) ∧ ∀ a, p a h → post a h,
  by grind⟩

def HeapM.exhale (hp : hProp) : HeapM Unit := ⟨fun post _ => hp ∗ post (),
  by grind⟩

def HeapM.inhale (hp : hProp) : HeapM Unit :=
⟨fun post _ => hp -∗ post (),
  by grind⟩

def HeapM.read (x : Loc) : HeapM Val :=
  pickSuchThat fun v h => h[x]?.any (·.1 = v)

def HeapM.assign (x : Loc) (v : Val) : HeapM Unit := do
  exhale perm(x)
  inhale (x ↦ v)


def HeapM.alloc (v : Val) : HeapM Loc := do
  let newKey ← pickSuchThat (· ∉ ·)
  inhale (newKey ↦ v)
  return newKey



instance : WPMonad HeapM hProp EPost⟨⟩ where
  wpTrans x post _ := ∀ʰ H, H -∗ x.val (fun x=> (H ∗ (post x))) epost⟨⟩
  wp_trans_pure x post _   :=
  by
    intro h post' hpost
    simp_all [pure, hWand, hExists, hPure] <;> constructor; constructor
    try apply post'
    constructor <;> rfl
    apply Heap.union_empty
    apply Heap.Disjoint.empty_right
  wp_trans_bind x f post _ :=
  by
    apply hForall_intro; intro H
    apply hForall_elim H (Q := H -∗ _)
    apply hWand_mono
    simp[bind]
    apply x.property
    rfl
    intro x
    simp
    apply hForall_star_elim
    apply hWand_elim

  wp_trans_monotone x :=
  by
    intro post post' epost epost' hpost hpost' H
    apply hForall_intro
    intro H
    apply hForall_elim H (Q := H -∗ _)
    apply hWand_mono
    apply x.property
    grind
    simp[PartialOrder.rel]
    intro x v HH
    simp_all[hStar]
    cases HH with
    |  intro h₁ h₂ hH hP hunion hdisj =>
       constructor
       apply hH
       apply hpost'
       apply hP
       apply hunion
       apply hdisj


theorem HeapM.frame (H pre : hProp) (post : α → hProp) (x : HeapM α) :
  ⦃ pre ⦄ x ⦃ post ⦄ →
  ⦃ H ∗ pre ⦄ x ⦃ v, H ∗ post v ⦄ :=
  by
    intro hpre
    apply Triple.iff.mpr
    have hwp := Triple.iff.mp hpre
    unfold wp
    unfold wp at hwp
    unfold wpTrans
    unfold wpTrans at hwp
    simp_all[instWPMonadHeapMHPropNil]
    apply hForall_intro
    intro H_1
    apply entails_hWand
    intro heap h_heap
    have step1 := hStar_assoc_r heap h_heap
    have step2 := hStar_mono hwp heap step1
    have step3 : (x.val (fun v => (H_1 ∗ H) ∗ post v) epost⟨⟩) heap :=
    hForall_star_elim (H_1 ∗ H) (P := fun H' => H' -∗ x.val (fun v => H' ∗ post v) epost⟨⟩) hWand_elim heap step2
    revert step3
    apply x.property
    rfl
    intro v
    exact hStar_assoc_l






theorem HeapM.inhale_spec (hp : hProp) :
  ⦃ ∅ ⦄ inhale hp ⦃ _, hp ⦄ := by
  simp [inhale]
  apply Triple.iff.mpr
  unfold wp
  unfold wpTrans
  simp_all[instWPMonadHeapMHPropNil]
  apply hForall_intro
  intro H
  apply entails_hWand
  apply entails_hWand
  -- trivial
  sorry










theorem HeapM.exhale_spec (hp : hProp) :
  hp ⊑ hp' →
  ⦃ hp ⦄ exhale hp' ⦃ _, ∅ ⦄ := by sorry

theorem HeapM.read_spec (x : Loc) (v : Val) :
  ⦃ x ↦ v ⦄ read x ⦃ v, ⌜v = v⌝ʰ ∗ x ↦ v ⦄ := by sorry


theorem HeapM.assign_spec (x : Loc) (v u : Val) :
  ⦃ x ↦ u ⦄ assign x v ⦃ _, x ↦ v ⦄ := by
  sorry

#print Triple

theorem HeapM.alloc_spec (v : Val) :
  ⦃ ∅ ⦄ alloc v ⦃ l, l ↦ v ⦄ := by
  sorry
