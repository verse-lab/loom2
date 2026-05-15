import Loom.Triple.Basic
import Loom.WP.Lemmas
import Plausible.Gen
import Plausible.Testable


open Lean.Order Std.Do'

section MonadTransformers

variable {m : Type → Type v} {Pred EPred : Type _}
variable [Monad m] [LawfulMonad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]

/-
  post st
  <-> wp id (fun _ => post) st
  <-> wp (get >>= set) (fun _ => post) st =
  <-> wp get (fun s => wp (set s) (fun _ => post)) st =
  <-> ∀ s, wp (m := Id) (get s) (fun ss => wp (m := Id) (set ss.1 ss.2) (fun _ => post)) st
  <-> ∀ s, post s
-/
noncomputable instance (priority := high) IgnoreState [Inhabited σ] :
  WPMonad (StateT σ m) Pred EPred where
  wpTrans x := ⟨fun post epost => ⨅ s, wp (m := m) (x s) (post ·.1) epost⟩
  wp_trans_pure x := by
    intro post epost
    apply le_iInf
    intro s
    exact WPMonad.wp_pure (m := m) (x, s) (post ·.1) epost
  wp_trans_bind x f := by
    intro post epost
    apply le_iInf
    intro s
    apply PartialOrder.rel_trans _ (WPMonad.wp_bind (m := m) (x s) ..)
    apply PartialOrder.rel_trans (iInf_le _ s)
    apply WPMonad.wp_consequence (m := m)
    intro x
    exact iInf_le _ x.2
  wp_trans_monotone x := by
    intro post post' epost epost' hepost hpost
    apply le_iInf
    intro s
    apply PartialOrder.rel_trans (iInf_le _ s)
    apply WPMonad.wp_consequence_econs (m := m) (x := x s)
    · intro x; apply hpost
    · exact hepost

noncomputable instance (priority := high) IgnoreReader [Inhabited ρ] :
  WPMonad (ReaderT ρ m) Pred EPred where
  wpTrans x := ⟨fun post epost => ⨅ r, wp (m := m) (x r) post epost⟩
  wp_trans_pure x := by
    intro post epost
    apply le_iInf
    intro r
    exact WPMonad.wp_pure (m := m) x post epost
  wp_trans_bind x f := by
    intro post epost
    apply le_iInf
    intro r
    apply PartialOrder.rel_trans _ (WPMonad.wp_bind (m := m) (x r) ..)
    apply PartialOrder.rel_trans (iInf_le _ r)
    apply WPMonad.wp_consequence (m := m)
    intro x
    exact iInf_le _ r
  wp_trans_monotone x := by
    intro post post' epost epost' hepost hpost
    apply le_iInf
    intro r
    apply PartialOrder.rel_trans (iInf_le _ r)
    apply WPMonad.wp_consequence_econs (m := m) (x r)
    · intro x; apply hpost
    · exact hepost

end MonadTransformers

instance (priority := high) : WPMonad (Except ε) Prop EPost⟨⟩ where
  wpTrans x := ⟨fun post _epost => match x with
    | .ok x => post x
    | .error _ => False⟩
  wp_trans_pure x := PartialOrder.rel_refl
  wp_trans_bind x f := by intro post epost; cases x <;> exact id
  wp_trans_monotone x := by
    intro post post' epost epost' hepost hpost
    cases x with
    | ok a => exact hpost a
    | error e => exact id

open Plausible

theorem chooseAny_wp (post : α → Prop) [Random Id α] :
  ⦃ ∀ a, post a ⦄ Gen.chooseAny α ⦃ a, post a ⦄ := by
  rw [Triple.iff]
  intro hpost
  simp [Gen.chooseAny, liftM, monadLift, wp, WPMonad.wpTrans]
  solve_by_elim

theorem Testable.run_wp [Testable p] :
  ⦃ p ∧ post ⦄ Testable.runPropE p c m ⦃ _, post ⦄ := by
  rw [Triple.iff]; intro ⟨ph, posth⟩
  simp [Testable.runPropE]; apply WPMonad.wp_bind (m := Gen)
  simp [tryCatch, MonadExceptOf.tryCatch, tryCatchThe, Except.tryCatch]
  simp [wp, WPMonad.wpTrans]
  intro s r
  cases hrun : (((fun a => DoResultPR.pure a PUnit.unit) <$> Testable.runProp p c m) s r) with
  | ok a =>
      rcases a with ⟨r, s'⟩
      cases r <;> simp [pure, StateT.pure, ReaderT.pure, Except.pure, posth]
  | error e =>
      simp [pure, StateT.pure, ReaderT.pure, Except.pure, posth]
