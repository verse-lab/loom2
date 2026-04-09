import Loom.Instances.HeapProp

open Lean.Order Loom


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

def HeapM.skip : HeapM Unit :=
  { predTrans := fun post _ => post () }

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


theorem HeapM.triple_skip_spec {P : hProp} :
    ⦃ P ⦄ HeapM.skip ⦃ _, P ⦄ := by
  exact Triple.pure () (PartialOrder.rel_refl)

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
  ⦃ x ↦ v ⦄ read x ⦃ v', ⌜v = v'⌝ʰ ∗ x ↦ v ⦄ := by
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
        · have key : (h₁.addUnion (Heap.single x v)).lookup x = some (v, 1) := by
            have h₁x : h₁.val x = none := eq₁
            simp [Heap.lookup, Heap.addUnion, Heap.single, h₁x]
          simp [Heap.lookup] at key
          rw [key] at hP
          simp at hP
          grind
        · have eq₂ : (Heap.single x v).lookup x = some (v, 1) := by
            simp [Heap.lookup_single]
          have ⟨hval, _⟩ := hdisj x v₁ p₁ v 1 eq₁ eq₂
          have h₁x : h₁.val x = some (v₁, p₁) := eq₁
          have key : (h₁.addUnion (Heap.single x v)).lookup x = some (v₁, p₁ + 1) := by
            simp [Heap.lookup, Heap.addUnion, Heap.single, h₁x]
          simp [Heap.lookup] at key
          rw [key] at hP
          simp at hP
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



theorem HeapM.read_frac_spec (x : Loc) (v : Val)
    (π : Perm) :
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
      · have eq₂ : (Heap.singleFrac x v π).lookup x = some (v, π) := by simp [Heap.lookup_singleFrac]
        have ⟨hval, _⟩ := hdisj x v₁ p₁ v π eq₁ eq₂
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
        · have key : (h₁.addUnion (Heap.singleFrac x v π)).lookup x = some (v, π) := by
            have h₁x : h₁.val x = none := eq₁
            simp [Heap.lookup, Heap.addUnion, Heap.singleFrac, h₁x]
          simp [Heap.lookup] at key
          rw [key] at hP
          simp at hP
          apply hP
        · have eq₂ : (Heap.singleFrac x v π).lookup x = some (v, π) := by
            simp [Heap.lookup_singleFrac]
          have ⟨hval, _⟩ := hdisj x v₁ p₁ v π eq₁ eq₂
          have h₁x : h₁.val x = some (v₁, p₁) := eq₁
          have key : (h₁.addUnion (Heap.singleFrac x v π)).lookup x = some (v₁, p₁ + π) := by
            simp [Heap.lookup, Heap.addUnion, Heap.singleFrac, h₁x]
          simp [Heap.lookup] at key
          rw [key] at hP
          simp at hP
          grind
    simp [empty_True, ← vv']
    exact HH
