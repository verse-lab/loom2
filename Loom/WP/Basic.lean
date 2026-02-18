import Loom.PredTrans

open Lean.Order

namespace Loom

/-!
# WP typeclass

The WP typeclass defines weakest precondition semantics for monads.
-/

universe u v w

class WP (m : Type u → Type v) (l : outParam (Type w)) (e : outParam (Type w))
    [Monad m] [CompleteLattice l] [CompleteLattice e] extends LawfulMonad m where
  wpImpl : m α → PredTrans l e α
  wp_pure_impl (x : α) (post : α → l) (epost : e) :
    post x ⊑ wpImpl (pure (f := m) x) post epost
  wp_bind_impl (x : m α) (f : α → m β) (post : β → l) (epost : e) :
    wpImpl x (fun x => wpImpl (f x) post epost) epost ⊑ wpImpl (x >>= f) post epost

@[reducible] def wp [Monad m] [CompleteLattice l] [CompleteLattice e] [WP m l e] {α} (x : m α) : PredTrans l e α :=
  WP.wpImpl x

theorem WP.wp_pure [Monad m] [CompleteLattice l] [CompleteLattice e] [WP m l e]
    (x : α) (post : α → l) (epost : e) :
    post x ⊑ wp (pure (f := m) x) post epost := by apply wp_pure_impl

theorem WP.wp_bind [Monad m] [CompleteLattice l] [CompleteLattice e] [WP m l e]
    (x : m α) (f : α → m β) (post : β → l) (epost : e) :
    wp x (fun x => wp (f x) post epost) epost ⊑ wp (x >>= f) post epost := by apply wp_bind_impl

theorem WP.wp_cons [Monad m] [CompleteLattice l] [CompleteLattice e] [WP m l e]
    (x : m α) (post post' : α → l) (epost : e)
    (h : ∀ a, post a ⊑ post' a) :
    wp x post epost ⊑ wp x post' epost :=
  (WP.wpImpl x).mono post post' epost epost h PartialOrder.rel_refl

variable {m : Type u → Type v} {l : Type w} {e : Type w}
    [Monad m] [CompleteLattice l] [CompleteLattice e] [WP m l e]

section DerivedTheorems

/-!
# Derived theorems for WP

We prove one direction of the derived theorems wp_map and wp_seq. The full bidirectional
equality theorems from Std/Do cannot be proven with our current axioms since wp_bind only
gives one direction (⊑). The reverse direction would require additional axioms.
-/

theorem WP.wp_map (f : α → β) (x : m α) :
  ∀ post epost, wp x (fun a => post (f a)) epost ⊑ wp (f <$> x) post epost := by
  intro post epost
  rw [← bind_pure_comp]
  apply PartialOrder.rel_trans
  · exact WP.wp_cons (m := m) x _ _ epost (fun a => WP.wp_pure (m := m) (f a) post epost)
  · exact WP.wp_bind x (pure ∘ f) post epost

theorem WP.wp_map' (f : α → β) (x : m α) :
  ∀ post post' epost (_ : post = fun a => post' (f a)), wp x post epost ⊑ wp (f <$> x) post' epost := by
  intro post post' epost h
  subst h
  apply wp_map

theorem WP.wp_seq (f : m (α → β)) (x : m α) :
  ∀ post epost, wp f (fun g => wp x (fun a => post (g a)) epost) epost ⊑ wp (f <*> x) post epost := by
  intro post epost
  rw [← bind_map]
  apply PartialOrder.rel_trans _ (WP.wp_bind f (fun g => g <$> x) post epost)
  apply (WP.wpImpl f).mono
  · intro g; exact WP.wp_map g x post epost
  · exact PartialOrder.rel_refl

end DerivedTheorems

/-!
# WP instances
-/

/-
  Except ε α --> WP (Except ε) Prop ((ε → Prop) × PUnit)

  Except ε α --> WP (Except ε) Prop (ε → Prop)

  -----
  Approach 1: have two instances for ExceptT ε m
    - `WP (ExceptT ε m) l (ε → l)` if we can derive `WP (ExceptT ε m) l Unit`
    - `WP (ExceptT ε m) l (e × (ε → l))` if we cannot derive `WP (ExceptT ε m) l Unit`

  Approach 2: change `e` to `List` of `{ tp: Type | x : tp }`


-/

instance Id.instWP : WP Id.{u} Prop Unit where
  wpImpl x := ⟨fun post _epost => post x, fun _ _ _ _ hpost _ => hpost x⟩
  wp_pure_impl x post epost := id
  wp_bind_impl x f post epost := by simp [bind]; exact PartialOrder.rel_refl

instance Option.instWP : WP Option Prop Prop where
  wpImpl x := ⟨fun post epost => x.elim epost post, by
    intro p1 p2 e1 e2 hp he
    cases x with
    | none => exact he
    | some a => exact hp a⟩
  wp_pure_impl x post epost := id
  wp_bind_impl x f post epost := by cases x <;> exact id

/--
Adds the ability to make assertions about exceptions of type `ε` to a predicate transformer with
postcondition shape `ps`, resulting in postcondition shape `.except ε ps`. This is done by
interpreting `ExceptT ε (PredTrans ps) α` into `PredTrans (.except ε ps) α`.

This can be used for all kinds of exception-like effects, such as early termination, by interpreting
them as exceptions.
-/
instance ExceptT.instWP {m : Type u → Type v} {l e : Type u}
    [Monad m] [CompleteLattice l] [CompleteLattice e] [WP m l e] :
    WP (ExceptT ε m) l ((ε → l) × e) where
  wpImpl x := PredTrans.pushExcept (wp x.run)
  wp_pure_impl x post epost :=
    WP.wp_pure (m := m) (Except.ok x) (PredTrans.pushExcept.post post epost) epost.2
  wp_bind_impl x f post epost := by
    simp only [PredTrans.apply_pushExcept, ExceptT.run_bind]
    apply PartialOrder.rel_trans _ (WP.wp_bind (m := m) x.run ..)
    apply WP.wp_cons (m := m)
    intro r; cases r with
    | ok a => exact PartialOrder.rel_refl
    | error err =>
      exact WP.wp_pure (m := m) (Except.error err) (PredTrans.pushExcept.post post epost) epost.2

@[simp, grind =]
theorem ExceptT.apply_wp {m : Type u → Type v} {l e : Type u}
    [Monad m] [CompleteLattice l] [CompleteLattice e] [WP m l e]
    (x : ExceptT ε m α) (post : α → l) (epost : (ε → l) × e) :
  (wp x) post epost = wp x.run (PredTrans.pushExcept.post post epost) epost.2 := rfl

instance StateT.instWP {m : Type u → Type v} {l e : Type u}
    [Monad m] [CompleteLattice l] [CompleteLattice e] [WP m l e] :
    WP (StateT σ m) (σ → l) e where
  wpImpl x := PredTrans.pushArg (wp ∘ x.run)
  wp_pure_impl x post epost s :=
    WP.wp_pure (m := m) (x, s) (fun ⟨a, s'⟩ => post a s') epost
  wp_bind_impl x f post epost := by
    intro s
    simp only [PredTrans.apply_pushArg, Function.comp_apply, StateT.run_bind]
    apply WP.wp_bind

@[simp, grind =]
theorem StateT.apply_wp {m : Type u → Type v} {l e : Type u}
    [Monad m] [CompleteLattice l] [CompleteLattice e] [WP m l e]
    (x : StateT σ m α) (post : α → σ → l) (epost : e) (s : σ) :
  (wp x) post epost s = wp (x.run s) (fun (a, s) => post a s) epost := rfl

instance ReaderT.instWP {m : Type u → Type v} {l e : Type u}
    [Monad m] [CompleteLattice l] [CompleteLattice e] [WP m l e] :
    WP (ReaderT ρ m) (ρ → l) e where
  wpImpl x := PredTrans.pushArg (fun r => (·, r) <$> wp (x.run r))
  wp_pure_impl x post epost r :=
    WP.wp_pure (m := m) x (fun a => post a r) epost
  wp_bind_impl x f post epost := by
    intro r
    simp only [PredTrans.apply_pushArg, PredTrans.apply_map, ReaderT.run_bind]
    apply PartialOrder.rel_trans
    · apply WP.wp_cons (m := m)
      intro a
      exact PartialOrder.rel_refl
    · apply WP.wp_bind

@[simp, grind =]
theorem ReaderT.apply_wp {m : Type u → Type v} {l e : Type u}
    [Monad m] [CompleteLattice l] [CompleteLattice e] [WP m l e]
    (x : ReaderT ρ m α) (post : α → ρ → l) (epost : e) (r : ρ) :
  (wp x) post epost r = wp (x.run r) (fun a => post a r) epost := rfl

/-
TODO: Same as for pushExcept
instance OptionT.instWP {l : Type u}
  [CompleteLattice l] [Monad m] [LawfulMonad m] [WP m l e] :
  WP (OptionT m) l (e × l) where
  wpImpl x post epost := WP.wp (m := m) (l := l) (e := e) x.run
    (fun o => match o with | some a => post a | none => epost.2)
    epost.1
  wp_pure x post epost := by
    simp [pure, OptionT.pure, OptionT.mk, OptionT.run, WP.wp_pure (m := m)]
  wp_bind x f post epost := by
    simp only [bind, OptionT.bind, OptionT.mk, OptionT.run]
    apply PartialOrder.rel_trans _ (WP.wp_bind (m := m) x ..)
    apply WP.wp_cons (m := m)
    intro o; cases o with
    | some a => exact PartialOrder.rel_refl
    | none => simp [WP.wp_pure (m := m)]; exact PartialOrder.rel_refl
  wp_cons x post post' epost h := by
    apply WP.wp_cons (m := m)
    intro o
    cases o with
    | some a => exact h a
    | none => exact PartialOrder.rel_refl
-/

/-!
# Type alias instances
-/

-- Except is a simple sum type, so error continuation is just ε → Prop
instance Except.instWP : WP (Except ε) Prop ((ε → Prop) × PUnit) where
  wpImpl x := ⟨fun post epost => match x with
    | .ok a => post a
    | .error e => epost.1 e, by
    intro p1 p2 e1 e2 hp he
    cases x with
    | ok a => exact hp a
    | error e => exact he.1 e⟩
  wp_pure_impl x post epost := id
  wp_bind_impl x f post epost := by cases x <;> exact id

-- EStateM combines state and exceptions
instance EStateM.instWP : WP (EStateM ε σ) (σ → Prop) (ε → σ → Prop) where
  wpImpl x := ⟨fun post epost s => match x s with
    | .ok a s' => post a s'
    | .error e s' => epost e s', by
    intro p1 p2 e1 e2 hp he s
    show (match x s with | .ok a s' => p1 a s' | .error e s' => e1 e s') →
         (match x s with | .ok a s' => p2 a s' | .error e s' => e2 e s')
    cases x s with
    | ok a s' => exact hp a s'
    | error e s' => exact he e s'⟩
  wp_pure_impl x post epost s := id
  wp_bind_impl x f post epost := by
    intro s
    show (match x s with | .ok a s' => _ | .error e s' => _) →
         (match match x s with | .ok a s => f a s | .error e s => .error e s with
          | .ok a s' => _ | .error e s' => _)
    cases x s with
    | ok a s' => exact id
    | error e s' => exact id

/-!
# Adequacy lemmas
-/

theorem Id.of_wp_run_eq {α : Type} {x : α} {prog : Id α}
  (h : Id.run prog = x) (P : α → Prop)
  (hwp : wp prog P ()) : P x := by
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
  (hwp : wp prog (fun a s' => P (a, s')) () s) : P x := by
  rw [← h]; simp only [wp, WP.wpImpl] at hwp; exact hwp

theorem StateM.of_wp_run'_eq {α σ : Type} {x : α} {prog : StateM σ α} {s : σ}
  (h : StateT.run' prog s = x) (P : α → Prop)
  (hwp : wp prog (fun a _ => P a) () s) : P x := by
  rw [← h]; simp only [wp, WP.wpImpl] at hwp; exact hwp

theorem ReaderM.of_wp_run_eq {α ρ : Type} {x : α} {prog : ReaderM ρ α} {r : ρ}
  (h : ReaderT.run prog r = x) (P : α → Prop)
  (hwp : wp prog (fun a _ => P a) () r) : P x := by
  rw [← h]; simp only [wp, WP.wpImpl] at hwp; exact hwp

theorem Except.of_wp_eq {ε α : Type} {x prog : Except ε α}
  (h : prog = x) (P : Except ε α → Prop)
  (hwp : wp prog (fun a => P (.ok a)) (fun e => P (.error e), .unit)) : P x := by
  subst h
  cases prog with
  | ok a => exact hwp
  | error e => exact hwp

theorem EStateM.of_wp_run_eq {ε σ α : Type} {x : EStateM.Result ε σ α} {prog : EStateM ε σ α} {s : σ}
  (h : EStateM.run prog s = x) (P : EStateM.Result ε σ α → Prop)
  (hwp : wp prog (fun a s' => P (.ok a s')) (fun e s' => P (.error e s')) s) : P x := by
  rw [← h]
  simp [wp, WP.wpImpl] at hwp -- TODO: Probably should define a simp lemma for impl of `wp`
  change P (prog s)
  cases heq : prog s with
  | ok a s' => simp [heq] at hwp; exact hwp
  | error e s' => simp [heq] at hwp; exact hwp

end Loom
