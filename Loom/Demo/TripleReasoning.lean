import Loom.Demo.HeapM

open Lean.Order Std.Do'
open scoped Std.Do'


theorem HeapM.triple_inhale {P H : hProp} {rest : HeapM α} {Q : α → hProp}
    (h : ⦃ P ∗ H ⦄ rest ⦃ Q ⦄) :
    ⦃ P ⦄ (do HeapM.inhale H; rest) ⦃ Q ⦄ :=
  Triple.bind _ _ (fun _ => P ∗ H)
    (by rw [← hStar_empty (H := P)]
        rw [((by simp) : ((P ∗ ∅) ∗ H = P ∗ H))]
        apply HeapM.frame P ∅ (fun _ => H) _ (inhale_spec H))
    (fun _ => h)

theorem HeapM.triple_exhale {P H R : hProp} {rest : HeapM α} {Q : α → hProp}
    (hsplit : P = H ∗ R)
    (h : ⦃ R ⦄ rest ⦃ Q ⦄) :
    ⦃ P ⦄ (do HeapM.exhale H; rest) ⦃ Q ⦄ :=
  Triple.bind _ _ (fun _ => R)
    (by subst hsplit
        have := HeapM.frame R H (fun _ => ∅) _ (exhale_spec H (by rfl))
        simp [hStar_comm] at this; exact this)
    (fun _ => h)



theorem HeapM.triple_inhale_done {P H : hProp} :
    ⦃ P ⦄ HeapM.inhale H ⦃ _, P ∗ H ⦄ := by
  rw [← hStar_empty (H := P)]
  rw [((by simp) : ((P ∗ ∅) ∗ H = P ∗ H))]
  exact HeapM.frame P ∅ (fun _ => H) _ (inhale_spec H)

theorem HeapM.triple_exhale_done {H R : hProp} :
    ⦃ H ∗ R ⦄ HeapM.exhale H ⦃ _, R ⦄ := by
  have := HeapM.frame R H (fun _ => ∅) _ (exhale_spec H (by rfl))
  simp [hStar_comm] at this; exact this



theorem HeapM.triple_pre_eq {P P' : hProp} {Q : α → hProp} {c : HeapM α}
    (heq : P = P')
    (h : ⦃ P' ⦄ c ⦃ Q ⦄) :
    ⦃ P ⦄ c ⦃ Q ⦄ := by
  subst heq; exact h

theorem HeapM.triple_post_eq {P : hProp} {Q Q' : α → hProp} {c : HeapM α}
    (heq : ∀ a, Q a = Q' a)
    (h : ⦃ P ⦄ c ⦃ Q' ⦄) :
    ⦃ P ⦄ c ⦃ Q ⦄ := by
  have : Q = Q' := funext heq
  subst this; exact h

theorem HeapM.triple_consequence {P P' : hProp} {Q Q' : α → hProp} {c : HeapM α}
    (hpre : P ⊑ P')
    (hpost : ∀ a, Q' a ⊑ Q a)
    (h : ⦃ P' ⦄ c ⦃ Q' ⦄) :
    ⦃ P ⦄ c ⦃ Q ⦄ :=
  Triple.iff.mpr (Triple.entails_wp_of_pre_post h hpre hpost)

theorem hPure_star_elim {P : Prop} {H : hProp} :
    ⌜P⌝ʰ ∗ H ⊑ H := by
  intro h hPH
  cases hPH with
  | intro h₁ h₂ hP hH hunion _ =>
    cases hP
    rw [Heap.empty_addUnion] at hunion
    exact hunion ▸ hH

theorem hStar_hPure_elim {P : Prop} {H : hProp} :
    H ∗ ⌜P⌝ʰ ⊑ H := by
  rw [hStar_comm]
  exact hPure_star_elim

theorem HeapM.triple_read_done (x : Loc) (v : Val) :
    ⦃ x ↦ v ⦄ HeapM.read x ⦃ w, ⌜v = w⌝ʰ ∗ x ↦ v ⦄ :=
  HeapM.read_spec x v

theorem HeapM.triple_read {rest : Val → HeapM α} {Q : α → hProp}
    (x : Loc) (v : Val)
    (h : ∀ w, ⦃ ⌜v = w⌝ʰ ∗ x ↦ v ⦄ rest w ⦃ Q ⦄) :
    ⦃ x ↦ v ⦄ (do let w ← HeapM.read x; rest w) ⦃ Q ⦄ :=
  Triple.bind _ _ (fun w => ⌜v = w⌝ʰ ∗ x ↦ v)
    (HeapM.triple_read_done x v)
    h

theorem HeapM.triple_read_eq {rest : Val → HeapM α} {Q : α → hProp}
    (x : Loc) (v : Val)
    (h : ⦃ x ↦ v ⦄ rest v ⦃ Q ⦄) :
    ⦃ x ↦ v ⦄ (do let w ← HeapM.read x; rest w) ⦃ Q ⦄ := by
  apply HeapM.triple_read x v
  intro w
  by_cases hvw : v = w
  · subst w
    exact HeapM.triple_consequence hPure_star_elim (fun _ => PartialOrder.rel_refl) h
  · apply Triple.iff.mpr
    intro heap hpre
    cases hpre with
    | intro h₁ h₂ hP _ _ _ =>
      cases hP with
      | intro hpure =>
        exact False.elim (hvw hpure)

theorem HeapM.triple_read_frame_done (F : hProp) (x : Loc) (v : Val) :
    ⦃ F ∗ (x ↦ v) ⦄ HeapM.read x ⦃ w, F ∗ (⌜v = w⌝ʰ ∗ x ↦ v) ⦄ :=
  HeapM.frame F (x ↦ v) (fun w => ⌜v = w⌝ʰ ∗ x ↦ v) _ (HeapM.read_spec x v)

theorem HeapM.triple_read_frame {rest : Val → HeapM α} {Q : α → hProp}
    (F : hProp) (x : Loc) (v : Val)
    (h : ∀ w, ⦃ F ∗ (⌜v = w⌝ʰ ∗ x ↦ v) ⦄ rest w ⦃ Q ⦄) :
    ⦃ F ∗ (x ↦ v) ⦄ (do let w ← HeapM.read x; rest w) ⦃ Q ⦄ :=
  Triple.bind _ _ (fun w => F ∗ (⌜v = w⌝ʰ ∗ x ↦ v))
    (HeapM.triple_read_frame_done F x v)
    h

theorem HeapM.triple_read_frame_eq {rest : Val → HeapM α} {Q : α → hProp}
    (F : hProp) (x : Loc) (v : Val)
    (h : ⦃ F ∗ (x ↦ v) ⦄ rest v ⦃ Q ⦄) :
    ⦃ F ∗ (x ↦ v) ⦄ (do let w ← HeapM.read x; rest w) ⦃ Q ⦄ := by
  apply HeapM.triple_read_frame F x v
  intro w
  by_cases hvw : v = w
  · subst w
    exact HeapM.triple_consequence (hStar_mono hPure_star_elim) (fun _ => PartialOrder.rel_refl) h
  · apply Triple.iff.mpr
    intro heap hpre
    cases hpre with
    | intro h₁ h₂ _ hinner _ _ =>
      cases hinner with
      | intro h₃ h₄ hP _ _ _ =>
        cases hP with
        | intro hpure =>
          exact False.elim (hvw hpure)

theorem HeapM.triple_assign_done (x : Loc) (old new : Val) :
    ⦃ x ↦ old ⦄ HeapM.assign x new ⦃ _, x ↦ new ⦄ :=
  HeapM.assign_spec x new old

theorem HeapM.triple_assign {rest : HeapM α} {Q : α → hProp}
    (x : Loc) (old new : Val)
    (h : ⦃ x ↦ new ⦄ rest ⦃ Q ⦄) :
    ⦃ x ↦ old ⦄ (do HeapM.assign x new; rest) ⦃ Q ⦄ :=
  Triple.bind _ _ (fun _ => x ↦ new)
    (HeapM.triple_assign_done x old new)
    (fun _ => h)

theorem HeapM.triple_assign_frame_done (F : hProp) (x : Loc) (old new : Val) :
    ⦃ F ∗ (x ↦ old) ⦄ HeapM.assign x new ⦃ _, F ∗ (x ↦ new) ⦄ :=
  HeapM.frame F (x ↦ old) (fun _ => x ↦ new) _ (HeapM.assign_spec x new old)

theorem HeapM.triple_assign_frame {rest : HeapM α} {Q : α → hProp}
    (F : hProp) (x : Loc) (old new : Val)
    (h : ⦃ F ∗ (x ↦ new) ⦄ rest ⦃ Q ⦄) :
    ⦃ F ∗ (x ↦ old) ⦄ (do HeapM.assign x new; rest) ⦃ Q ⦄ :=
  Triple.bind _ _ (fun _ => F ∗ (x ↦ new))
    (HeapM.triple_assign_frame_done F x old new)
    (fun _ => h)





theorem HeapM.triple_exhale_frac {P : hProp} {rest : HeapM α} {Q : α → hProp}
    (x : Loc) (v : Val) (π_exhale π_keep : Perm)
    (hv_exhale : π_exhale.IsValid) (hv_keep : π_keep.IsValid)
    (hsum : π_exhale + π_keep = 1)
    (hpre : P = x ↦ v)
    (h : ⦃ x ↦[π_keep] v ⦄ rest ⦃ Q ⦄) :
    ⦃ P ⦄ (do HeapM.exhale (x ↦[π_exhale] v); rest) ⦃ Q ⦄ :=
  HeapM.triple_exhale
    (R := x ↦[π_keep] v)
    (by rw [hpre, hSingleFrac_split x v π_exhale π_keep hv_exhale hv_keep hsum])
    h

theorem HeapM.triple_exhale_frac_of_frac {P : hProp} {rest : HeapM α} {Q : α → hProp}
    (x : Loc) (v : Val) (π_have π_exhale π_keep : Perm)
    (hv_exhale : π_exhale.IsValid) (hv_keep : π_keep.IsValid)
    (hsum : π_exhale + π_keep = π_have)
    (hv_have : π_have.IsValid)
    (hpre : P = x ↦[π_have] v)
    (h : ⦃ x ↦[π_keep] v ⦄ rest ⦃ Q ⦄) :
    ⦃ P ⦄ (do HeapM.exhale (x ↦[π_exhale] v); rest) ⦃ Q ⦄ :=
  HeapM.triple_exhale
    (R := x ↦[π_keep] v)
    (by rw [hpre, hSingleFrac_combine x v π_exhale π_keep hv_exhale hv_keep (by rw [hsum]; exact hv_have), hsum])
    h

theorem HeapM.triple_exhale_from_star {F : hProp} {rest : HeapM α} {Q : α → hProp}
    (x : Loc) (v : Val) (π_have π_exhale π_keep : Perm)
    (hv_exhale : π_exhale.IsValid) (hv_keep : π_keep.IsValid)
    (hsum : π_exhale + π_keep = π_have)
    (hv_have : π_have.IsValid)
    (h : ⦃ F ∗ (x ↦[π_keep] v) ⦄ rest ⦃ Q ⦄) :
    ⦃ F ∗ (x ↦[π_have] v) ⦄ (do HeapM.exhale (x ↦[π_exhale] v); rest) ⦃ Q ⦄ :=
  HeapM.triple_exhale
    (R := F ∗ (x ↦[π_keep] v))
    (by rw [← hsum, ← hSingleFrac_combine x v π_exhale π_keep hv_exhale hv_keep (hsum ▸ hv_have),
            ← hStar_assoc, hStar_comm (H₁ := F), hStar_assoc])
    h




example (p : Loc) (v : Val) :
    ⦃ ∅ ⦄
    (do HeapM.inhale (p ↦ v)
        HeapM.exhale (p ↦[Perm.third] v))
    ⦃ _, p ↦[Perm.twoThirds] v ⦄ := by
  apply Triple.iff.mpr
  unfold wp WPMonad.wpTrans
  simp_all [instWPMonadHeapMHPropNil]
  apply hForall_intro
  intro H
  apply entails_hWand
  simp [Bind.bind, HeapM.bind, HeapM.inhale, HeapM.exhale]
  apply entails_hWand
  intro heap HH
  rw [hSingleFrac_split p v Perm.third Perm.twoThirds
    (by grind) (by grind)] at HH
  rotate_right
  grind
  revert HH heap
  rw[hStar_assoc]
  simp [hStar_comm]




example (p : Loc) (v : Val) :
    ⦃ ∅ ⦄
    (do HeapM.inhale (p ↦ v)
        HeapM.exhale (p ↦[Perm.third] v)
        HeapM.exhale (p ↦[Perm.third] v)
        HeapM.skip)
    ⦃ _, p ↦[{val:=1/3}] v ⦄ := by
  apply HeapM.triple_inhale
  apply HeapM.triple_pre_eq
  { simp; rfl }
  apply HeapM.triple_exhale_frac p v Perm.third Perm.twoThirds
    (by grind) (by grind) (by ext; grind) rfl
  apply HeapM.triple_exhale_frac_of_frac p v Perm.twoThirds Perm.third Perm.third
    (by grind) (by grind) (by ext; grind) (by grind) rfl
  apply HeapM.triple_skip_spec

example (p : Loc) (v : Val) :
    ⦃ ∅ ⦄
    (do HeapM.inhale (p ↦ v)
        let _ ← HeapM.read p
        HeapM.skip)
    ⦃ _, p ↦ v ⦄ := by
  apply HeapM.triple_inhale
  apply HeapM.triple_pre_eq (P' := p ↦ v)
  · simp
  apply HeapM.triple_read_eq p v
  apply HeapM.triple_skip_spec

example (p : Loc) (old new : Val) :
    ⦃ ∅ ⦄
    (do HeapM.inhale (p ↦ old)
        HeapM.assign p new)
    ⦃ _, p ↦ new ⦄ := by
  apply HeapM.triple_inhale
  apply HeapM.triple_pre_eq (P' := p ↦ old)
  · simp
  exact HeapM.triple_assign_done p old new

example (p : Loc) (v : Val) :
    ⦃ ∅ ⦄
    (do HeapM.inhale (p ↦ v)
        let w ← HeapM.read p
        HeapM.assign p (w + 1))
    ⦃ _, p ↦ (v + 1) ⦄ := by
  apply HeapM.triple_inhale
  apply HeapM.triple_pre_eq (P' := p ↦ v)
  · simp
  apply HeapM.triple_read_eq p v
  exact HeapM.triple_assign_done p v (v + 1)

example (p q : Loc) (vp vq : Val) :
    ⦃ (q ↦ vq) ∗ (p ↦ vp) ⦄
    (do let w ← HeapM.read p
        HeapM.assign p (w + 1)
        HeapM.skip)
    ⦃ _, (q ↦ vq) ∗ (p ↦ (vp + 1)) ⦄ := by
  apply HeapM.triple_read_frame_eq (q ↦ vq) p vp
  apply HeapM.triple_assign_frame
  apply HeapM.triple_skip_spec
