import Loom.Defs
-- import Loom.LatticeExt

open Lean.Order

attribute [simp] PartialOrder.rel_refl

instance instWPMonadId : WPMonad Id Prop Empty where
  wp x post epost := post x
  wp_pure x post epost := rfl
  wp_bind x f post epost := by simp [bind]
  wp_cons x post post' epost h := by apply h
  -- wp_econs x post epost epost' h := by exact id

instance instWPMonadOption : WPMonad Option Prop PUnit where
  wp x post epost := x.elim (epost ⟨⟩) post
  wp_pure x post epost := rfl
  wp_bind x f post epost := by cases x <;> exact id
  wp_cons x post post' epost h := by cases x with
    | none => exact id
    | some a => exact h a

instance instWPMonadExcept {l : Type u}
  [CompleteLattice l] [Monad m] [WPMonad m l ε] : WPMonad (ExceptT ε' m) l (ε ⊕' ε') where
  wp x post epost := WPMonad.wp (m := m) (l := l) (ε := ε) x
    (fun | .ok x => post x | .error e => epost (.inr e))
    (fun e => epost (.inl e))
  wp_pure x post epost := by simp [pure, ExceptT.pure, ExceptT.mk, WPMonad.wp_pure]
  wp_bind x f post epost := by
    simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.run]
    apply PartialOrder.rel_trans _ (WPMonad.wp_bind (m := m) (l := l) (ε := ε) x _ _ _)
    apply WPMonad.wp_cons (m := m) (l := l) (ε := ε)
    intro r; cases r with
    | ok a => exact PartialOrder.rel_refl
    | error e => simp [ExceptT.bindCont, WPMonad.wp_pure (m := m) (l := l) (ε := ε)]
  wp_cons x post post' epost h := by
    apply WPMonad.wp_cons (m := m) (l := l) (ε := ε)
    intro r; cases r with
    | ok a => exact h a
    | error e => exact PartialOrder.rel_refl

instance instWPMonadStateT {l : Type u}
  [CompleteLattice l] [Monad m] [WPMonad m l ε] : WPMonad (StateT σ m) (σ -> l) (ε × σ) where
  wp x post epost := fun s => WPMonad.wp (m := m) (l := l) (ε := ε) (x s)
    (fun x => post x.1 x.2)
    (fun x => by )
  wp_pure x post epost := by funext s; simp [pure, StateT.pure, WPMonad.wp_pure (m := m)]
  wp_bind x f post epost := by
    intro s
    simp only [bind, StateT.bind]
    -- The issue: LHS has epost applied to intermediate states, RHS to initial state
    -- This requires monotonicity in the error continuation
    -- We need wp_econs (like wp_cons but for error continuations)
    apply PartialOrder.rel_trans; rotate_left
    { exact WPMonad.wp_bind (x s) (fun p => f p.1 p.2) (fun r => post r.1 r.2) (epost · s) }
    apply WPMonad.wp_cons


  wp_cons x post post' epost h := by
    intro s
    apply WPMonad.wp_cons (m := m) (l := l) (ε := ε)
    intro ⟨a, s'⟩
    exact h a s'

instance instWPMonadStateT {l : Type u}
  [CompleteLattice l] [Monad m] [WPMonad m l ε] : WPMonad (StateT σ m) (σ -> l) ε where
  wp x post epost := fun s => WPMonad.wp (m := m) (l := l) (ε := ε) (x s)
    (fun x => post x.1 x.2)
    (epost · s)
  wp_pure x post epost := by funext s; simp [pure, StateT.pure, WPMonad.wp_pure (m := m)]
  wp_bind x f post epost := by
    intro s
    simp only [bind, StateT.bind]
    -- The issue: LHS has epost applied to intermediate states, RHS to initial state
    -- This requires monotonicity in the error continuation
    -- We need wp_econs (like wp_cons but for error continuations)
    apply PartialOrder.rel_trans; rotate_left
    { exact WPMonad.wp_bind (x s) (fun p => f p.1 p.2) (fun r => post r.1 r.2) (epost · s) }
    apply WPMonad.wp_cons


  wp_cons x post post' epost h := by
    intro s
    apply WPMonad.wp_cons (m := m) (l := l) (ε := ε)
    intro ⟨a, s'⟩
    exact h a s'
