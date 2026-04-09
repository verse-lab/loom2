import Loom.Instances.HeapM

open Lean.Order Loom


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




#check @Perm.ext
example (p : Loc) (v : Val) :
    ⦃ ∅ ⦄
    (do HeapM.inhale (p ↦ v)
        HeapM.exhale (p ↦[Perm.third] v))
    ⦃ _, p ↦[Perm.twoThirds] v ⦄ := by
  apply Triple.iff.mpr
  unfold wp wpTrans
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
        HeapM.inhale (p ↦ v)
        HeapM.exhale (p ↦[Perm.third] v)
        HeapM.exhale (p ↦[Perm.third] v)
        HeapM.skip)
    ⦃ _, p ↦[Perm.third] v ⦄ := by
  apply Triple.iff.mpr
  unfold wp wpTrans
  simp_all [instWPMonadHeapMHPropNil]
  apply hForall_intro
  intro H
  apply entails_hWand
  simp [Bind.bind, HeapM.bind, HeapM.inhale, HeapM.exhale, HeapM.skip]
  sorry


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
