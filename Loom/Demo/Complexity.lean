import Loom.Triple.Basic
import Loom.WP.Lemmas
import Loom.Frame

open Lean.Order Std.Do'

abbrev Credit := Nat

abbrev WithCredit (Pred : Type u) := Credit → Pred

structure CreditT (m : Type u → Type v) (α : Type u) where
  run : Credit → m (α × Credit)

namespace CreditT

-- variable {α β : Type u}

@[ext] theorem ext {m : Type u → Type v} {α : Type u} {x y : CreditT m α}
    (h : ∀ c, x.run c = y.run c) : x = y := by
  cases x
  cases y
  congr
  funext c
  exact h c

protected def map [Monad m] (f : α → β) (x : CreditT m α) : CreditT m β :=
  ⟨StateT.map f x.run⟩

protected def pure [Monad m] (x : α) : CreditT m α :=
  ⟨StateT.pure x⟩

protected def bind [Monad m] (x : CreditT m α) (f : α → CreditT m β) : CreditT m β :=
  ⟨StateT.bind x.run fun a => (f a).run⟩

instance [Monad m] : Monad (CreditT m) where
  map := CreditT.map
  pure := CreditT.pure
  bind := CreditT.bind

instance [Monad m] [LawfulMonad m] : LawfulMonad (CreditT m) :=
  LawfulMonad.mk' (CreditT m)
    (id_map := by
      intro α x
      ext c
      simp [Functor.map, CreditT.map, StateT.map])
    (pure_bind := by
      intro α β x f
      ext c
      simp [Bind.bind, Pure.pure, CreditT.bind, CreditT.pure, StateT.bind, StateT.pure])
    (bind_assoc := by
      intro α β γ x f g
      ext c
      simp [Bind.bind, CreditT.bind, StateT.bind])
    (bind_pure_comp := by
      intro α β f x
      ext c
      simp [Bind.bind, Pure.pure, Functor.map, CreditT.bind, CreditT.map, CreditT.pure,
        StateT.bind, StateT.map, StateT.pure])

end CreditT

-- variable {m : Type u → Type v} {Pred : Type u} {EPred : Type u}

noncomputable instance [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
  WPMonad (CreditT m) (WithCredit Pred) EPred where
  wpTrans {α} x := ⟨fun post epost crd =>
    ⨅ crdFrame,
       wp (x.run (crd + crdFrame)) (fun ⟨ret, crd'⟩ => ⌜ crd' ≥ crdFrame ⌝ ⊓ post ret (crd' - crdFrame)) epost⟩
  wp_trans_pure x := by
    intro post epost crd
    apply le_iInf
    intro crdFrame
    apply PartialOrder.rel_trans
    · exact le_meet (post x crd) (⌜crd + crdFrame ≥ crdFrame⌝) (post x (crd + crdFrame - crdFrame))
        (le_pure _ _ (Nat.le_add_left crdFrame crd))
        (by
          have hsub : crd + crdFrame - crdFrame = crd := Nat.add_sub_cancel crd crdFrame
          rw [hsub])
    · exact WPMonad.wp_pure (m := m) (x, crd + crdFrame)
        (fun ⟨ret, crd'⟩ => ⌜crd' ≥ crdFrame⌝ ⊓ post ret (crd' - crdFrame)) epost
  wp_trans_bind x f := by
    intro post epost crd
    apply le_iInf
    intro crdFrame
    apply PartialOrder.rel_trans (iInf_le _ crdFrame)
    apply PartialOrder.rel_trans
    · apply WPMonad.wp_consequence (m := m) (x := x.run (crd + crdFrame))
      intro ret
      rw [pure_intro_r]
      intro hcrd
      apply PartialOrder.rel_trans (iInf_le _ crdFrame)
      have hrun : ret.2 - crdFrame + crdFrame = ret.2 := Nat.sub_add_cancel hcrd
      rw [hrun]
    · simpa [Bind.bind, CreditT.bind, StateT.bind] using
        (WPMonad.wp_bind (m := m) (x := x.run (crd + crdFrame))
          (f := fun ret => (f ret.1).run ret.2)
          (post := fun ⟨ret, crd'⟩ => ⌜crd' ≥ crdFrame⌝ ⊓ post ret (crd' - crdFrame))
          epost)
  wp_trans_monotone x := by
    intro post post' epost epost' hepost hpost crd
    apply le_iInf
    intro crdFrame
    apply PartialOrder.rel_trans (iInf_le _ crdFrame)
    apply WPMonad.wp_consequence_econs (m := m) (x := x.run (crd + crdFrame))
    · intro ret
      apply le_meet
      · exact meet_le_left _ _
      · exact PartialOrder.rel_trans (meet_le_right _ _) (hpost ret.1 (ret.2 - crdFrame))
    · exact hepost

abbrev cProp := WithCredit Prop

noncomputable def cStar [CompleteLattice Pred]
    (H1 H2 : WithCredit Pred) : WithCredit Pred :=
  fun x => iSup fun x1 => ⌜x1 ≤ x⌝ ⊓ (H1 x1 ⊓ H2 (x - x1))

infixl:65 " ∗ᶜ " => cStar

noncomputable def cStarValue [CompleteLattice Pred]
    (H1 H2 : WithCredit Pred) (val : Credit) : WithCredit Pred :=
  fun x => ⌜val ≤ x⌝ ⊓ (H1 val ⊓ H2 (x - val))

noncomputable def cStarQ [CompleteLattice Pred]
    (H1 : α → WithCredit Pred) (H2 : WithCredit Pred): α → WithCredit Pred :=
  fun a x => cStar (H1 a) H2 x

noncomputable def cPure [CompleteLattice Pred] (h : Prop) : WithCredit Pred :=
  fun x => ⌜x = 0 ∧ h⌝

noncomputable def cCredit [CompleteLattice Pred] (H : Credit → Prop) : WithCredit Pred :=
  fun x => ⌜H x⌝

notation:max "⌜" H "⌝ᶜ" => cCredit H

noncomputable def cVal [CompleteLattice Pred] (x : Int) : WithCredit Pred :=
  fun x₁ => ⌜(x₁ : Int) ≤ x⌝

def cImpl [CompleteLattice Pred] (H1 H2 : WithCredit Pred) : Prop :=
  H1 ⊑ H2

noncomputable def cEq [CompleteLattice Pred] (x : Int) : WithCredit Pred :=
  fun x₁ => ⌜x = (x₁ : Int)⌝

noncomputable def cWand' [CompleteLattice Pred]
    (H1 H2 : WithCredit Pred) : WithCredit Pred :=
  fun x => iInf fun x1 => H1 x1 ⇨ H2 (x + x1)

infixr:60 " -∗ᶜ " => cWand'

noncomputable def cWandQ [CompleteLattice Pred]
    (H1 H2 : α → WithCredit Pred) : WithCredit Pred :=
  fun x => iInf fun a => cWand' (H1 a) (H2 a) x

namespace CreditT

theorem frame [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (H : Credit → Prop) (pre : WithCredit Pred) (post : α → WithCredit Pred)
    (epost : EPred) (x : CreditT m α) :
    Triple pre x post epost →
    Triple (⌜H⌝ᶜ ∗ᶜ pre) x (fun a => ⌜H⌝ᶜ ∗ᶜ post a) epost := by
  intro htriple
  rw [Triple.iff] at htriple ⊢
  intro crd
  unfold cStar cCredit
  apply iSup_le
  intro crdFrame
  rw [pure_intro_r]
  intro hframe_le
  rw [pure_intro_r]
  intro hframe
  apply PartialOrder.rel_trans
  · exact htriple (crd - crdFrame)
  apply le_iInf
  intro crdFrame'
  apply PartialOrder.rel_trans (iInf_le _ (crdFrame' + crdFrame))
  have hrun : crd - crdFrame + (crdFrame' + crdFrame) = crd + crdFrame' := by
    rw [Nat.add_comm crdFrame' crdFrame, ← Nat.add_assoc, Nat.sub_add_cancel hframe_le]
  rw [hrun]
  apply WPMonad.wp_consequence (m := m)
  intro ret
  apply le_meet
  · apply PartialOrder.rel_trans (meet_le_left _ _)
    exact LE.pure_imp _ _ (fun hret =>
      Nat.le_trans (Nat.le_add_right crdFrame' crdFrame) hret)
  · rw [pure_intro_r]
    intro hret
    apply PartialOrder.rel_trans _ (le_iSup (fun x1 =>
      ⌜x1 ≤ ret.2 - crdFrame'⌝ ⊓ (⌜H x1⌝ ⊓ post ret.1 (ret.2 - crdFrame' - x1))) crdFrame)
    apply le_meet
    · apply le_pure
      exact Nat.le_sub_of_add_le' hret
    · apply le_meet
      · exact le_pure _ _ hframe
      · have hpost :
            ret.2 - crdFrame' - crdFrame = ret.2 - (crdFrame' + crdFrame) := by
          rw [Nat.sub_sub]
        rw [hpost]

end CreditT


/-
∀ʰ f, (= f) -∗ wp x (fun x => (= f) ∗ post x) epost

fun h => ∀ f, (= f) -∗ wp x (fun x => (= f) ∗ post x) epost h
fun h => ∀ f, wp x (fun x => (= f) ∗ post x) epost (h + f)
fun h => ∀ f, wp (x.run (x + f)) (fun x h => (= f) ∗ post x) epost (h + f)

-/
