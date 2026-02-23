import Loom.PredTrans

open Lean.Order

namespace Loom

universe u v
variable {m : Type u → Type v}

/-!
# WPMonad typeclass

The WPMonad typeclass defines weakest precondition semantics for monads.
-/

class WPMonad (m : Type u → Type v) (l : outParam (Type w)) (e : outParam (Type w))
    [Monad m] [CompleteLattice l] [CompleteLattice e] extends LawfulMonad m where
  wpTrans : m α → PredTrans l e α
  wp_trans_pure (x : α) : pure x ⊑ wpTrans (pure (f := m) x)
  wp_trans_bind (x : m α) (f : α → m β) : wpTrans x >>= (wpTrans ∘ f) ⊑ wpTrans (x >>= f)
  wp_trans_monotone (x : m α) : wpTrans x |>.monotone

def wp [Monad m] [CompleteLattice l] [CompleteLattice e] [WPMonad m l e] {α} (x : m α) (post : α → l) (epost : e) : l :=
  WPMonad.wpTrans x post epost

@[simp, grind =] theorem WPMonad.wp_impl_eq_wp [Monad m] [CompleteLattice l] [CompleteLattice e] [WPMonad m l e] {α} (x : m α):
    WPMonad.wpTrans x = wp x := rfl

theorem WPMonad.wp_pure [Monad m] [CompleteLattice l] [CompleteLattice e] [WPMonad m l e] (x : α) (post : α → l) (epost : e) :
    post x ⊑ wp (pure (f := m) x) post epost := by apply wp_trans_pure x

theorem WPMonad.wp_bind [Monad m] [CompleteLattice l] [CompleteLattice e] [WPMonad m l e] (x : m α) (f : α → m β) (post : β → l) (epost : e) :
    wp x (fun x => wp (f x) post epost) epost ⊑ wp (x >>= f) post epost := by apply wp_trans_bind x f

theorem WPMonad.wp_cons [Monad m] [CompleteLattice l] [CompleteLattice e] [WPMonad m l e] (x : m α) (post post' : α → l) (epost : e)
   (h : post ⊑ post') :
    wp x post epost ⊑ wp x post' epost := by solve_by_elim [WPMonad.wp_trans_monotone, PartialOrder.rel_refl]

theorem WPMonad.wp_cons' [Monad m] [CompleteLattice l] [CompleteLattice e] [WPMonad m l e] (x : m α) (post post' : α → l) (epost : e)
   (h : post ⊑ post') (h' : epost ⊑ epost') :
    wp x post epost ⊑ wp x post' epost' := by solve_by_elim [WPMonad.wp_trans_monotone]


/-!
# Derived theorems for WPMonad

We prove one direction of the derived theorems wp_map and wp_seq. The full bidirectional
equality theorems from Std/Do cannot be proven with our current axioms since wp_bind only
gives one direction (⊑). The reverse direction would require additional axioms.
-/

theorem WPMonad.wp_map [Monad m] [LawfulMonad m] [CompleteLattice l] [CompleteLattice e] [WPMonad m l e] (f : α → β) (x : m α) :
  ∀ post epost, wp x (fun a => post (f a)) epost ⊑ wp (f <$> x) post epost := by
  intro post epost
  rw [← bind_pure_comp]
  apply PartialOrder.rel_trans; rotate_left;
  exact WPMonad.wp_trans_bind x (pure ∘ f) post epost
  apply WPMonad.wp_cons
  intro a; exact WPMonad.wp_trans_pure (f a) post epost

theorem WPMonad.wp_map' [Monad m] [LawfulMonad m] [CompleteLattice l] [CompleteLattice e] [WPMonad m l e] (f : α → β) (x : m α) :
  ∀ post post' epost (_ : post = fun a => post' (f a)), wp x post epost ⊑ wp (f <$> x) post' epost := by
  intro post post' epost h
  subst h
  apply wp_map

theorem WPMonad.wp_seq [Monad m] [LawfulMonad m] [CompleteLattice l] [CompleteLattice e] [WPMonad m l e] (f : m (α → β)) (x : m α) :
  ∀ post epost, wp f (fun g => wp x (fun a => post (g a)) epost) epost ⊑ wp (f <*> x) post epost := by
  intro post epost
  rw [← bind_map]
  apply PartialOrder.rel_trans _ (WPMonad.wp_bind f (fun g => g <$> x) post epost)
  apply WPMonad.wp_cons; intro g; exact WPMonad.wp_map g x post epost

/-!
# WPMonad instances
-/

instance Id.instWPMonad : WPMonad Id.{u} Prop EPost.nil where
  wpTrans x := fun post _epost => post x
  wp_trans_pure _x := PartialOrder.rel_refl
  wp_trans_bind _x _f := PartialOrder.rel_refl
  wp_trans_monotone x := fun _ _ _ _ hpost _ => hpost x

instance Option.instWPMonad : WPMonad Option.{u} Prop Prop where
  wpTrans x := fun post epost => x.elim epost post
  wp_trans_pure x := PartialOrder.rel_refl
  wp_trans_bind x f := fun post epost => by cases x <;> exact id
  wp_trans_monotone x := fun post post' epost epost' hpost hepost => by
    cases x with
    | none => exact hepost
    | some a => exact hpost a

@[simp, grind =]
theorem apply_pushExcept {α ε l e} (x : PredTrans l e (Except ε α)) (post : α → l) (epost : EPost.cons (ε → l) e) :
  (PredTrans.pushExcept x) post epost = x (epost.pushExcept post) epost.tail := rfl

/- TODO: change the order of `(e × (ε → l))` -/
instance ExceptT.instWPMonad {l : Type u}
    [CompleteLattice l] [CompleteLattice e] [Monad m] [LawfulMonad m] [WPMonad m l e] :
    WPMonad (ExceptT ε m) l (EPost.cons (ε → l) e) where
  wpTrans x := PredTrans.pushExcept (wp x.run)
  wp_trans_pure x := fun post epost =>
    WPMonad.wp_pure (m := m) (Except.ok x) (epost.pushExcept post) epost.tail
  wp_trans_bind x f := fun post epost => by
    simp only [apply_pushExcept, ExceptT.run_bind]
    apply PartialOrder.rel_trans _ (WPMonad.wp_bind (m := m) x ..)
    apply WPMonad.wp_cons (m := m)
    · intro r; cases r with
      | ok a => exact PartialOrder.rel_refl
      | error e =>
        exact WPMonad.wp_pure (m := m) (Except.error e) (epost.pushExcept post) epost.tail
  wp_trans_monotone x := fun post post' epost epost' hpost hepost => by
    simp only [apply_pushExcept]
    apply WPMonad.wp_cons' (m := m)
    · intro r; cases r with
      | ok a => exact hpost a
      | error e => exact hepost.1 e
    · exact hepost.2

@[simp, grind =]
theorem ExceptT.apply_wp {α ε l e} [Monad m] [CompleteLattice l] [CompleteLattice e] [WPMonad m l e] (x : ExceptT ε m α) (post : α → l) (epost : EPost.cons (ε → l) e) :
  (wp x) post epost = wp x.run (epost.pushExcept post) epost.tail := rfl

instance StateT.instWPMonad {l : Type u}
  [CompleteLattice l] [CompleteLattice e] [Monad m] [LawfulMonad m] [WPMonad m l e] :
  WPMonad (StateT σ m) (σ -> l) e where
  wpTrans x := pushArg (wp ∘ x.run)
  wp_trans_pure x := fun post epost s =>
    WPMonad.wp_pure (m := m) (x, s) (fun p => post p.1 p.2) epost
  wp_trans_bind x f := fun post epost s => by
    simp only [apply_pushArg, Function.comp_apply, StateT.run_bind]
    apply WPMonad.wp_bind
  wp_trans_monotone x := fun post post' epost epost' hpost hepost s => by
    apply WPMonad.wp_cons' (m := m)
    · intro ⟨a, s'⟩; exact hpost a s'
    · exact hepost

@[simp, grind =]
theorem StateT.apply_wp {σ : Type u} [Monad m] [CompleteLattice l] [CompleteLattice e] [WPMonad m l e] (x : StateT σ m α) (post : α → σ → l) (epost : e) (s : σ) :
  (wp x) post epost s = wp (x.run s) (fun (a, s) => post a s) epost := rfl

instance ReaderT.instWPMonad {l : Type u}
    [CompleteLattice l] [CompleteLattice e] [Monad m] [LawfulMonad m] [WPMonad m l e] :
    WPMonad (ReaderT ρ m) (ρ → l) e where
  wpTrans x := fun post epost r => wp (x.run r) (fun a => post a r) epost
  wp_trans_pure x := fun post epost r =>
    WPMonad.wp_pure (m := m) x (fun a => post a r) epost
  wp_trans_bind x f := fun post epost r => by
    simp only [ReaderT.run_bind]
    apply PartialOrder.rel_trans
    · apply WPMonad.wp_cons' (m := m)
      · intro a; exact PartialOrder.rel_refl
      · exact PartialOrder.rel_refl
    · apply WPMonad.wp_bind
  wp_trans_monotone x := fun post post' epost epost' hpost hepost r => by
    apply WPMonad.wp_cons' (m := m)
    · intro a; exact hpost a r
    · exact hepost

@[simp, grind =]
theorem ReaderT.apply_wp {ρ : Type u} [Monad m] [CompleteLattice l] [CompleteLattice e] [WPMonad m l e] (x : ReaderT ρ m α) (post : α → ρ → l) (epost : e) (r : ρ) :
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
instance Except.instWPMonad : WPMonad (Except ε) Prop EPost⟨ε → Prop⟩ where
  wpTrans x := fun post epost => match x with
    | .ok a => post a
    | .error e => epost.head e
  wp_trans_pure x := PartialOrder.rel_refl
  wp_trans_bind x f := fun post epost => by cases x <;> exact id
  wp_trans_monotone x := fun post post' epost epost' hpost hepost => by
    cases x with
    | ok a => exact hpost a
    | error e => exact hepost.1 e

-- EStateM combines state and exceptions
instance EStateM.instWPMonad : WPMonad (EStateM ε σ) (σ → Prop) (ε → σ → Prop) where
  wpTrans x := fun post epost s => match x s with
    | .ok a s' => post a s'
    | .error e s' => epost e s'
  wp_trans_pure x := fun post epost s => PartialOrder.rel_refl
  wp_trans_bind x f := fun post epost s => by
    simp only [bind, EStateM.bind]
    cases (x s) <;> exact PartialOrder.rel_refl
  wp_trans_monotone x := fun post post' epost epost' hpost hepost s => by
    dsimp only []
    cases heq : x s with
    | ok a s' => exact hpost a s'
    | error e s' => exact hepost e s'

/-!
# Adequacy lemmas
-/

theorem Id.of_wp_run_eq {α : Type} {x : α} {prog : Id α}
  (h : Id.run prog = x) (P : α → Prop)
  (hwp : wp prog P EPost.nil.mk) : P x := by
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
  (hwp : wp prog (fun a s' => P (a, s')) EPost.nil.mk s) : P x := by
  rw [← h]
  exact hwp

theorem StateM.of_wp_run'_eq {α σ : Type} {x : α} {prog : StateM σ α} {s : σ}
  (h : StateT.run' prog s = x) (P : α → Prop)
  (hwp : wp prog (fun a _ => P a) EPost.nil.mk s) : P x := by
  rw [← h]
  exact hwp

theorem ReaderM.of_wp_run_eq {α ρ : Type} {x : α} {prog : ReaderM ρ α} {r : ρ}
  (h : ReaderT.run prog r = x) (P : α → Prop)
  (hwp : wp prog (fun a _ => P a) EPost.nil.mk r) : P x := by
  rw [← h]
  exact hwp

theorem Except.of_wp_eq {ε α : Type} {x prog : Except ε α}
  (h : prog = x) (P : Except ε α → Prop)
  (hwp : wp prog (fun a => P (.ok a)) epost⟨fun e => P (.error e)⟩) : P x := by
  subst h
  cases prog with
  | ok a => exact hwp
  | error e => exact hwp

theorem EStateM.of_wp_run_eq {ε σ α : Type} {x : EStateM.Result ε σ α} {prog : EStateM ε σ α} {s : σ}
  (h : EStateM.run prog s = x) (P : EStateM.Result ε σ α → Prop)
  (hwp : wp prog (fun a s' => P (.ok a s')) (fun e s' => P (.error e s')) s) : P x := by
  rw [← h]
  simp [wp, WPMonad.wpTrans] at hwp
  change P (prog s)
  cases heq : prog s with
  | ok a s' => simp [heq] at hwp; exact hwp
  | error e s' => simp [heq] at hwp; exact hwp

-- #check LawfulMonad
-- #check MonadStateOf
-- #check StateT

-- #check (_ : Type) -> Prop

-- class LawfulMonadStateOf (σ : Type) {l : Type} {m : Type → Type v} [MonadStateOf σ m] [Monad m] [CompleteLattice l] [WPMonad m l e] where
--   [σlift : MonadLift (PredTrans (σ → Prop) Unit) (PredTrans l e)]
--   wp_get : liftM (n := PredTrans l e) (m := PredTrans (σ → Prop) Unit) (wp (get : StateM σ σ)) ⊑ wp (get : m σ)
--   wp_set (s : σ) : liftM (n := PredTrans l e) (m := PredTrans (σ → Prop) Unit) (wp (set s : StateM σ PUnit)) ⊑ wp (set s : m PUnit)
--   wp_modifyGet (f : σ → α × σ) : liftM (n := PredTrans l e) (m := PredTrans (σ → Prop) Unit) (wp (modifyGet f : StateM σ α)) ⊑ wp (modifyGet f : m α)

-- class LawfulMonadReaderOf (ρ : Type) {l : Type} {m : Type → Type v} [MonadReaderOf ρ m] [Monad m] [CompleteLattice l] [WPMonad m l e] where
--   [ρlift : MonadLift (PredTrans (ρ → Prop) Unit) (PredTrans l e)]
--   wp_read : liftM (n := PredTrans l e) (m := PredTrans (ρ → Prop) Unit) (wp (read : ReaderM ρ ρ)) ⊑ wp (read : m ρ)

-- class LawfulMonadExceptOf (ε : Type) {l : Type} {m : Type → Type v} [MonadExceptOf ε m] [Monad m] [CompleteLattice l] [WPMonad m l e] where
--   [εlift : MonadLift (PredTrans (ε → Prop) Unit) (PredTrans l e)]
--   -- wp_throw (err : ε) : liftM (n := PredTrans l e) (m := PredTrans (ε → Prop) Unit) (wp (throw err : m (Except ε α))) ⊑ wp (throw err : m (Except ε α))
--   wp_tryCatch (x : m α) (h : PUnit → m α) : liftM (n := PredTrans l e) (m := PredTrans (ε → Prop) Unit) (wp (tryCatch x h : m α)) ⊑ wp (tryCatch x h : m α)


end Loom
