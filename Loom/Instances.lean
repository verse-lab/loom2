import Loom.WP.Basic

open Lean.Order

attribute [simp] PartialOrder.rel_refl

instance instWPMonadId : WPMonad Id Prop Unit where
  wp x post epost := post x
  wp_pure x post epost := rfl
  wp_bind x f post epost := by simp [bind]
  wp_cons x post post' epost h := by apply h
  -- wp_econs x post epost epost' h := by exact id

instance instWPMonadOption : WPMonad Option Prop Prop where
  wp x post epost := x.elim epost post
  wp_pure x post epost := rfl
  wp_bind x f post epost := by cases x <;> exact id
  wp_cons x post post' epost h := by cases x with
    | none => exact id
    | some a => exact h a

instance instWPMonadExcept {l : Type u}
  [CompleteLattice l] [Monad m] [WPMonad m l e] : WPMonad (ExceptT ε m) l (e × (ε → l)) where
  wp x post epost := WPMonad.wp (m := m) (l := l) (e := e) x
    (fun | .ok x => post x | .error e => epost.2 e)
    epost.1
  wp_pure x post epost := by simp [pure, ExceptT.pure, ExceptT.mk, WPMonad.wp_pure]
  wp_bind x f post epost := by
    simp only [bind, ExceptT.bind, ExceptT.mk]
    apply PartialOrder.rel_trans _ (WPMonad.wp_bind (m := m) x ..)
    apply WPMonad.wp_cons (m := m)
    intro r; cases r with
    | ok a => exact PartialOrder.rel_refl
    | error _ => simp [ExceptT.bindCont, WPMonad.wp_pure (m := m)]
  wp_cons x post post' epost h := by
    apply WPMonad.wp_cons
    intro r; cases r with
    | ok a => exact h a
    | error e => exact PartialOrder.rel_refl

instance instWPMonadStateT {l : Type u}
  [CompleteLattice l] [Monad m] [WPMonad m l e] : WPMonad (StateT σ m) (σ -> l) e where
  wp x post epost := fun s => WPMonad.wp (m := m) (l := l) (e := e) (x s)
    (fun x => post x.1 x.2)
    epost
  wp_pure x post epost := by funext s; simp [pure, StateT.pure, WPMonad.wp_pure (m := m)]
  wp_bind x f post epost := by
    intro s
    simp only [bind, StateT.bind]
    apply WPMonad.wp_bind
  wp_cons x post post' epost h := by
    intro s
    apply WPMonad.wp_cons
    intro ⟨a, s'⟩
    exact h a s'
