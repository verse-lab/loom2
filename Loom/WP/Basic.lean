import Loom.ECont

open Lean.Order

namespace Loom

universe u v
variable {m : Type u → Type v}

/-!
# WPMonad typeclass

The WPMonad typeclass defines weakest precondition semantics for monads.
-/

class WPMonad (m : Type u → Type v) (l : outParam (Type u)) (e : outParam (Type u)) [Monad m] [CompleteLattice l] where
  wp : m α → ECont l e α
  wp_pure (x : α) (post : α → l) (epost : e) : wp (pure (f := m) x) post epost = post x
  wp_bind (x : m α) (f : α → m β) (post : β → l) (epost : e) : wp x (fun x => wp (f x) post epost) epost ⊑ wp (x >>= f) post epost
  wp_cons (x : m α) (post post' : α → l) (epost : e) (h : post ⊑ post') : wp x post epost ⊑ wp x post' epost

export WPMonad (wp)

/-!
# Derived theorems for WPMonad

We prove one direction of the derived theorems wp_map and wp_seq. The full bidirectional
equality theorems from Std/Do cannot be proven with our current axioms since wp_bind only
gives one direction (⊑). The reverse direction would require additional axioms.
-/

theorem WPMonad.wp_map [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (f : α → β) (x : m α) :
  ∀ post epost, wp x (fun a => post (f a)) epost ⊑ wp (f <$> x) post epost := by
  intro post epost
  rw [← bind_pure_comp]
  have h : (fun a => post (f a)) = (fun a => wp (pure (f := m) (f a)) post epost) := by
    ext a
    simp [WPMonad.wp_pure]
  rw [h]
  exact WPMonad.wp_bind x (pure ∘ f) post epost

theorem WPMonad.wp_seq [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (f : m (α → β)) (x : m α) :
  ∀ post epost, wp f (fun g => wp x (fun a => post (g a)) epost) epost ⊑ wp (f <*> x) post epost := by
  intro post epost
  rw [← bind_map]
  apply PartialOrder.rel_trans _ (WPMonad.wp_bind f (fun g => g <$> x) post epost)
  apply WPMonad.wp_cons
  intro g
  exact WPMonad.wp_map g x post epost

/-!
# WPMonad instances
-/

instance Id.instWPMonad : WPMonad Id Prop Unit where
  wp x post epost := post x
  wp_pure x post epost := rfl
  wp_bind x f post epost := by simp [bind]; exact PartialOrder.rel_refl
  wp_cons x post post' epost h := by apply h

instance Option.instWPMonad : WPMonad Option Prop Prop where
  wp x post epost := x.elim epost post
  wp_pure x post epost := rfl
  wp_bind x f post epost := by cases x <;> exact id
  wp_cons x post post' epost h := by cases x with
    | none => exact id
    | some a => exact h a

instance ExceptT.instWPMonad {l : Type u}
  [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e] :
  WPMonad (ExceptT ε m) l (e × (ε → l)) where
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
    | error _ => simp [ExceptT.bindCont, WPMonad.wp_pure (m := m)]; exact PartialOrder.rel_refl
  wp_cons x post post' epost h := by
    apply WPMonad.wp_cons
    intro r; cases r with
    | ok a => exact h a
    | error e => exact PartialOrder.rel_refl

instance StateT.instWPMonad {l : Type u}
  [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e] :
  WPMonad (StateT σ m) (σ -> l) e where
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

instance ReaderT.instWPMonad {l : Type u}
  [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e] :
  WPMonad (ReaderT ρ m) (ρ → l) e where
  wp x post epost := fun r => WPMonad.wp (m := m) (l := l) (e := e) (x r)
    (fun a => post a r)
    epost
  wp_pure x post epost := by funext r; simp [pure, ReaderT.pure, WPMonad.wp_pure (m := m)]
  wp_bind x f post epost := by
    intro r
    simp only [bind, ReaderT.bind]
    apply PartialOrder.rel_trans
    · apply WPMonad.wp_cons (m := m)
      intro a
      exact PartialOrder.rel_refl
    · apply WPMonad.wp_bind (m := m)
  wp_cons x post post' epost h := by
    intro r
    apply WPMonad.wp_cons (m := m)
    intro a
    exact h a r

instance OptionT.instWPMonad {l : Type u}
  [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e] :
  WPMonad (OptionT m) l (e × l) where
  wp x post epost := WPMonad.wp (m := m) (l := l) (e := e) x.run
    (fun o => match o with | some a => post a | none => epost.2)
    epost.1
  wp_pure x post epost := by
    simp [pure, OptionT.pure, OptionT.mk, OptionT.run, WPMonad.wp_pure (m := m)]
  wp_bind x f post epost := by
    simp only [bind, OptionT.bind, OptionT.mk, OptionT.run]
    apply PartialOrder.rel_trans _ (WPMonad.wp_bind (m := m) x ..)
    apply WPMonad.wp_cons (m := m)
    intro o; cases o with
    | some a => exact PartialOrder.rel_refl
    | none => simp [WPMonad.wp_pure (m := m)]; exact PartialOrder.rel_refl
  wp_cons x post post' epost h := by
    apply WPMonad.wp_cons (m := m)
    intro o
    cases o with
    | some a => exact h a
    | none => exact PartialOrder.rel_refl

/-!
# Type alias instances
-/

-- For StateM, we use PUnit at universe u to match the universe requirements
instance State.instWPMonad : WPMonad (StateM σ) (σ → Prop) PUnit :=
  inferInstanceAs (WPMonad (StateT σ Id) (σ → Prop) PUnit)

instance Reader.instWPMonad : WPMonad (ReaderM ρ) (ρ → Prop) PUnit :=
  inferInstanceAs (WPMonad (ReaderT ρ Id) (ρ → Prop) PUnit)

-- Except is a simple sum type, so error continuation is just ε → Prop
instance Except.instWPMonad : WPMonad (Except ε) Prop (PUnit × (ε → Prop)) where
  wp x post epost := match x with
    | .ok a => post a
    | .error e => epost.2 e
  wp_pure x post epost := rfl
  wp_bind x f post epost := by cases x <;> exact id
  wp_cons x post post' epost h := by cases x with
    | ok a => exact h a
    | error e => exact id

-- EStateM combines state and exceptions
instance EStateM.instWPMonad : WPMonad (EStateM ε σ) (σ → Prop) (ε → σ → Prop) where
  wp x post epost := fun s => match x s with
    | .ok a s' => post a s'
    | .error e s' => epost e s'
  wp_pure x post epost := by
    funext s
    simp [pure, EStateM.pure]
  wp_bind x f post epost := by
    intro s
    simp only [bind, EStateM.bind]
    cases (x s) <;> exact PartialOrder.rel_refl
  wp_cons x post post' epost h := by
    intro s
    generalize heq : x s = r
    cases r with
    | ok a s' => simp [heq]; exact h a s'
    | error e s' => simp [heq]; exact PartialOrder.rel_refl

/-!
# Adequacy lemmas
-/

theorem Id.of_wp_run_eq {α : Type} {x : α} {prog : Id α}
  (h : Id.run prog = x) (P : α → Prop)
  (hwp : wp prog P PUnit.unit) : P x := by
  rw [← h]
  exact hwp

theorem Option.of_wp_eq {α : Type} {x prog : Option α}
  (h : prog = x) (P : Option α → Prop)
  (hwp : wp prog (fun a => P (some a)) (P none)) : P x := by
  subst h
  cases prog with
  | none => exact hwp
  | some a => exact hwp

theorem StateM.of_wp_run_eq {α σ : Type} {x : α × σ} {prog : StateM σ α} {s : σ}
  (h : StateT.run prog s = x) (P : α × σ → Prop)
  (hwp : wp prog (fun a s' => P (a, s')) PUnit.unit s) : P x := by
  rw [← h]
  exact hwp

theorem StateM.of_wp_run'_eq {α σ : Type} {x : α} {prog : StateM σ α} {s : σ}
  (h : StateT.run' prog s = x) (P : α → Prop)
  (hwp : wp prog (fun a _ => P a) PUnit.unit s) : P x := by
  rw [← h]
  exact hwp

theorem ReaderM.of_wp_run_eq {α ρ : Type} {x : α} {prog : ReaderM ρ α} {r : ρ}
  (h : ReaderT.run prog r = x) (P : α → Prop)
  (hwp : wp prog (fun a _ => P a) PUnit.unit r) : P x := by
  rw [← h]
  exact hwp

theorem Except.of_wp_eq {ε α : Type} {x prog : Except ε α}
  (h : prog = x) (P : Except ε α → Prop)
  (hwp : wp prog (fun a => P (.ok a)) (.unit, fun e => P (.error e))) : P x := by
  subst h
  cases prog with
  | ok a => exact hwp
  | error e => exact hwp

theorem EStateM.of_wp_run_eq {ε σ α : Type} {x : EStateM.Result ε σ α} {prog : EStateM ε σ α} {s : σ}
  (h : EStateM.run prog s = x) (P : EStateM.Result ε σ α → Prop)
  (hwp : wp prog (fun a s' => P (.ok a s')) (fun e s' => P (.error e s')) s) : P x := by
  rw [← h]
  simp only [wp] at hwp
  change P (prog s)
  cases heq : prog s with
  | ok a s' => simp [heq] at hwp; exact hwp
  | error e s' => simp [heq] at hwp; exact hwp

end Loom
