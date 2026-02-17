import Loom.ECont

open Lean.Order

namespace Loom

universe u v
variable {m : Type u → Type v}

/-!
# WPMonad typeclass

The WPMonad typeclass defines weakest precondition semantics for monads.
-/

class WPMonad (m : Type u → Type v) (l : outParam (Type w)) (e : outParam (Type w))
    [Monad m] [CompleteLattice l] extends LawfulMonad m where
  wpImpl : m α → ECont l e α
  wp_pure_impl (x : α) (post : α → l) (epost : e) :
    /- TODO: put ⊑ here  -/
    wpImpl (pure (f := m) x) post epost = post x
  wp_bind_impl (x : m α) (f : α → m β) (post : β → l) (epost : e) :
    wpImpl x (fun x => wpImpl (f x) post epost) epost ⊑ wpImpl (x >>= f) post epost
  wp_cons_impl (x : m α) (post post' : α → l) (epost : e) (h : post ⊑ post') :
    wpImpl x post epost ⊑ wpImpl x post' epost

def wp [Monad m] [CompleteLattice l] [WPMonad m l e] {α} (x : m α) (post : α → l) (epost : e) : l :=
  WPMonad.wpImpl x post epost

@[simp, grind =] theorem WPMonad.wp_impl_eq_wp [Monad m] [CompleteLattice l] [WPMonad m l e] {α} (x : m α):
    WPMonad.wpImpl x = wp x := rfl

theorem WPMonad.wp_pure [Monad m] [CompleteLattice l] [WPMonad m l e] (x : α) (post : α → l) (epost : e) :
    wp (pure (f := m) x) post epost = post x := by apply wp_pure_impl

theorem WPMonad.wp_bind [Monad m] [CompleteLattice l] [WPMonad m l e] (x : m α) (f : α → m β) (post : β → l) (epost : e) :
    wp x (fun x => wp (f x) post epost) epost ⊑ wp (x >>= f) post epost := by apply wp_bind_impl

theorem WPMonad.wp_cons [Monad m] [CompleteLattice l] [WPMonad m l e] (x : m α) (post post' : α → l) (epost : e) (h : post ⊑ post') :
    wp x post epost ⊑ wp x post' epost := by apply wp_cons_impl _ _ _ _ h

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

theorem WPMonad.wp_map' [Monad m] [LawfulMonad m] [CompleteLattice l] [WPMonad m l e] (f : α → β) (x : m α) :
  ∀ post post' epost (_ : post = fun a => post' (f a)), wp x post epost ⊑ wp (f <$> x) post' epost := by
  intro post post' epost h
  subst h
  apply wp_map

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

/-
  Except ε α --> WPMonad (Except ε) Prop ((ε → Prop) × PUnit)

  Except ε α --> WPMonad (Except ε) Prop (ε → Prop)

  -----
  Approach 1: have two instances for ExceptT ε m
    - `WPMonad (ExceptT ε m) l (ε → l)` if we can derive `WPMonad (ExceptT ε m) l Unit`
    - `WPMonad (ExceptT ε m) l (e × (ε → l))` if we cannot derive `WPMonad (ExceptT ε m) l Unit`

  Approach 2: change `e` to `List` of `{ tp: Type | x : tp }`


-/

instance Id.instWPMonad : WPMonad Id.{u} Prop Unit where
  wpImpl x post epost := post x
  wp_pure_impl x post epost := rfl
  wp_bind_impl x f post epost := by simp [bind]; exact PartialOrder.rel_refl
  wp_cons_impl x post post' epost h := by apply h

-- #check Id.instWPMonad


instance Option.instWPMonad : WPMonad Option Prop Prop where
  wpImpl x post epost := x.elim epost post
  wp_pure_impl x post epost := rfl
  wp_bind_impl x f post epost := by cases x <;> exact id
  wp_cons_impl x post post' epost h := by cases x with
    | none => exact id
    | some a => exact h a

/--
Adds the ability to make assertions about exceptions of type `ε` to a predicate transformer with
postcondition shape `ps`, resulting in postcondition shape `.except ε ps`. This is done by
interpreting `ExceptT ε (PredTrans ps) α` into `PredTrans (.except ε ps) α`.

This can be used for all kinds of exception-like effects, such as early termination, by interpreting
them as exceptions.
-/
/- TODO: change the order of `(e × (ε → l))` -/
def pushExcept {α ε l e} (x : ECont l e (Except ε α)) : ECont l (e × (ε → l)) α :=
  fun post epost => x (fun | .ok a => post a | .error e => epost.2 e) epost.1

abbrev pushExcept.post {l : Type u} (post : α → l) (epost : e × (ε → l)) : Except ε α → l :=
  fun | .ok a => post a | .error e => epost.2 e

@[simp, grind =]
theorem apply_pushExcept {α ε l e} (x : ECont l e (Except ε α)) (post : α → l) (epost : e × (ε → l)) :
  (pushExcept x) post epost = x (pushExcept.post post epost) epost.1 := rfl

/- TODO: change the order of `(e × (ε → l))` -/
instance ExceptT.instWPMonad {l : Type u}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e] :
    WPMonad (ExceptT ε m) l (e × (ε → l)) where
  wpImpl x := pushExcept (wp x.run)
  wp_pure_impl x post epost := by simp [WPMonad.wp_pure]
  wp_bind_impl x f post epost := by
    simp only [apply_pushExcept, ExceptT.run_bind]
    apply PartialOrder.rel_trans _ (WPMonad.wp_bind (m := m) x ..)
    apply WPMonad.wp_cons (m := m)
    intro r; cases r with
    | ok a => exact PartialOrder.rel_refl
    | error _ => simp [WPMonad.wp_pure (m := m)]; exact PartialOrder.rel_refl
  wp_cons_impl x post post' epost h := by
    apply WPMonad.wp_cons
    intro r; cases r with
    | ok a => exact h a
    | error e => exact PartialOrder.rel_refl

@[simp, grind =]
theorem ExceptT.apply_wp {α ε l e} [Monad m] [CompleteLattice l] [WPMonad m l e] (x : ExceptT ε m α) (post : α → l) (epost : e × (ε → l)) :
  (wp x) post epost = wp x.run (pushExcept.post post epost) epost.1 := rfl

/--
Adds the ability to make assertions about a state of type `σ` to a predicate transformer with
postcondition shape `ps`, resulting in postcondition shape `.arg σ ps`. This is done by
interpreting `StateT σ (PredTrans ps) α` into `PredTrans (.arg σ ps) α`.

This can be used to for all kinds of state-like effects, including reader effects or append-only
states, by interpreting them as states.
-/
-- Think: modifyGetM
def pushArg {σ : Type u} (x : σ → ECont l e (α × σ)) : ECont (σ → l) e α :=
  fun post epost s => x s (fun (a, s) => post a s) epost

@[simp, grind =]
theorem apply_pushArg {σ : Type u} (x : σ → ECont l e (α × σ)) (post : α → σ → l) (epost : e) (s : σ) :
  (pushArg x) post epost s = x s (fun (a, s) => post a s) epost := rfl

instance StateT.instWPMonad {l : Type u}
  [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e] :
  WPMonad (StateT σ m) (σ -> l) e where
  wpImpl x := pushArg (wp ∘ x.run)
  wp_pure_impl x post epost := by ext s; simp [WPMonad.wp_pure]
  wp_bind_impl x f post epost := by
    intro s
    simp only [apply_pushArg, Function.comp_apply, StateT.run_bind]
    apply WPMonad.wp_bind
  wp_cons_impl x post post' epost h := by
    intro s
    apply WPMonad.wp_cons
    intro ⟨a, s'⟩
    exact h a s'

@[simp, grind =]
theorem StateT.apply_wp {σ : Type u} [Monad m] [CompleteLattice l] [WPMonad m l e] (x : StateT σ m α) (post : α → σ → l) (epost : e) (s : σ) :
  (wp x) post epost s = wp (x.run s) (fun (a, s) => post a s) epost := rfl

instance ReaderT.instWPMonad {l : Type u}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e] :
    WPMonad (ReaderT ρ m) (ρ → l) e where
  wpImpl x := pushArg (fun r => (·, r) <$> wp (x.run r))
  wp_pure_impl x post epost := by ext r; simp [WPMonad.wp_pure]
  wp_bind_impl x f post epost := by
    intro r
    simp only [apply_pushArg, ECont.apply_map, ReaderT.run_bind]
    apply PartialOrder.rel_trans
    · apply WPMonad.wp_cons (m := m)
      intro a
      exact PartialOrder.rel_refl
    · apply WPMonad.wp_bind
  wp_cons_impl x post post' epost h := by
    intro r
    apply WPMonad.wp_cons (m := m)
    intro a
    exact h a r

@[simp, grind =]
theorem ReaderT.apply_wp {ρ : Type u} [Monad m] [CompleteLattice l] [WPMonad m l e] (x : ReaderT ρ m α) (post : α → ρ → l) (epost : e) (r : ρ) :
  (wp x) post epost r = wp (x.run r) (fun a => post a r) epost := rfl

/-
TODO: Same as for pushExcept
instance OptionT.instWPMonad {l : Type u}
  [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e] :
  WPMonad (OptionT m) l (e × l) where
  wpImpl x post epost := WPMonad.wp (m := m) (l := l) (e := e) x.run
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
-/

/-!
# Type alias instances
-/

-- Except is a simple sum type, so error continuation is just ε → Prop
instance Except.instWPMonad : WPMonad (Except ε) Prop (PUnit × (ε → Prop)) where
  wpImpl x post epost := match x with
    | .ok a => post a
    | .error e => epost.2 e
  wp_pure_impl x post epost := rfl
  wp_bind_impl x f post epost := by cases x <;> exact id
  wp_cons_impl x post post' epost h := by cases x with
    | ok a => exact h a
    | error e => exact id

-- EStateM combines state and exceptions
instance EStateM.instWPMonad : WPMonad (EStateM ε σ) (σ → Prop) (ε → σ → Prop) where
  wpImpl x post epost := fun s => match x s with
    | .ok a s' => post a s'
    | .error e s' => epost e s'
  wp_pure_impl x post epost := by
    funext s
    simp [wp, pure, EStateM.pure]
  wp_bind_impl x f post epost := by
    intro s
    simp only [wp, bind, EStateM.bind]
    cases (x s) <;> exact PartialOrder.rel_refl
  wp_cons_impl x post post' epost h := by
    intro s
    generalize heq : x s = r
    cases r with
    | ok a s' => simp [wp, heq]; exact h a s'
    | error e s' => simp [wp, heq]; exact PartialOrder.rel_refl

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
  simp [wp, WPMonad.wpImpl] at hwp -- TODO: Probably should define a simp lemma for impl of `wp`
  change P (prog s)
  cases heq : prog s with
  | ok a s' => simp [heq] at hwp; exact hwp
  | error e s' => simp [heq] at hwp; exact hwp

end Loom
