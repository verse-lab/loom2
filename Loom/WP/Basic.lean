/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Loom.PredTrans
universe u v w z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order Std.Do'

/-!
# Weakest Precondition Interpretation

This module defines the weakest precondition interpretation `WPMonad` of monadic programs
in terms of predicate transformers `PredTrans`.

An instance `WPMonad m l el` determines a function `wpTrans : m α → PredTrans l el α` that
interprets a program `x : m α` as a predicate transformer. The function `wp` is the
user-facing wrapper: `wp x post epost` computes the weakest precondition for `x` to
satisfy normal postcondition `post` and exception postcondition `epost`.

## Assertion Language Classes

`AssertionLang` and `ExceptAssertionLang` are both just alias type classes for `CompleteLattice`.
We introduce them for readability: `AssertionLang l` marks `l` as the assertion language for
normal postconditions, while `ExceptAssertionLang e` marks `e` as the type of exception
postconditions.

## Pre-defined instances

* `WPMonad Id Prop EPost.nil` — pure computations.
* `WPMonad (StateT σ m) (σ → l) el` — stateful computations.
* `WPMonad (ExceptT ε m) l (EPost.cons (ε → l) el)` — computations with exceptions.
* `WPMonad (ReaderT ρ m) (ρ → l) el` — reader computations.
* `WPMonad (Except ε) Prop EPost⟨ε → Prop⟩` — concrete exception type.
* `WPMonad (EStateM ε σ) (σ → Prop) (ε → σ → Prop)` — concrete error-state monad.
-/

namespace Std.Do'

variable {m : Type u → Type z}

/-- An assertion language is a type equipped with a `CompleteLattice` structure,
used as the carrier for pre- and postconditions. -/
class abbrev AssertionLang (l : Type w) := CompleteLattice l

/-- An exception assertion language is a type equipped with a `CompleteLattice` structure,
used for exception postcondition types. -/
class abbrev ExceptAssertionLang (e : Type w) := CompleteLattice e

/-- An exception assertion language is a chain-complete partial order. -/
scoped instance [ExceptAssertionLang e] : CCPO e where
  has_csup {c} _ := CompleteLattice.has_sup c

/-!
## WPMonad Typeclass

The `WPMonad` typeclass defines weakest precondition semantics for monads.
A `WPMonad m l el` instance provides a monad morphism `wpTrans : m α → PredTrans l el α`
satisfying:
- `wp_trans_pure`: `pure x` is at least as strong as its predicate transformer.
- `wp_trans_bind`: sequential composition is sound.
- `wp_trans_monotone`: the transformer is monotone in both postconditions.
-/

/-- Weakest precondition monad: a monad `m` with a sound interpretation as predicate
transformers over assertion language `l` with exception postconditions `el`. -/
class WPMonad (m : Type u → Type v) (l : outParam (Type w)) (el : outParam (Type w'))
    [Monad m] [AssertionLang l] [ExceptAssertionLang el] extends LawfulMonad m where
  /-- The weakest precondition transformer for a monadic program. -/
  wpTrans : m α → PredTrans l el α
  /-- Soundness of `pure`: the postcondition applied to `x` implies the WP of `pure x`. -/
  wp_trans_pure (x : α) : pure x ⊑ wpTrans (pure (f := m) x)
  /-- Soundness of `bind`: composing WPs is at least as strong as the WP of `>>=`. -/
  wp_trans_bind (x : m α) (f : α → m β) :
    wpTrans x >>= (wpTrans <| f ·) ⊑ wpTrans (x >>= f)
  /-- Monotonicity: weaker postconditions yield weaker preconditions. -/
  wp_trans_monotone (x : m α) : wpTrans x |>.monotone

/-- Compute the weakest precondition of `x` for normal postcondition `post` and
exception postcondition `epost`. -/
def wp [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] {α} (x : m α) (post : α → l) (epost : el) : l :=
  WPMonad.wpTrans x post epost

@[simp, grind =] theorem WPMonad.wp_impl_eq_wp [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] {α} (x : m α) :
  WPMonad.wpTrans x = wp x := rfl

/-!
## Derived WP Lemmas

One-directional consequences of the `WPMonad` axioms for `pure`, `bind`, monotonicity,
and weakening.
-/

theorem WPMonad.wp_pure [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] (x : α) (post : α → l) (epost : el) :
  post x ⊑ wp (pure (f := m) x) post epost := by apply wp_trans_pure x

theorem WPMonad.wp_bind [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] (x : m α) (f : α → m β)
  (post : β → l) (epost : el) :
    wp x (fun x => wp (f x) post epost) epost ⊑ wp (x >>= f) post epost := by
  apply wp_trans_bind x f

theorem WPMonad.wp_cons [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] (x : m α)
  (post post' : α → l) (epost : el) (h : post ⊑ post') :
    wp x post epost ⊑ wp x post' epost := by
  solve_by_elim [WPMonad.wp_trans_monotone, PartialOrder.rel_refl]

theorem WPMonad.wp_cons_econs [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] (x : m α)
  (post post' : α → l) (epost epost' : el) (h : post ⊑ post') (h' : epost ⊑ epost') :
    wp x post epost ⊑ wp x post' epost' := by
  exact WPMonad.wp_trans_monotone x post post' epost epost' h' h

theorem WPMonad.wp_econs [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] (x : m α)
  (post : α → l) (epost epost' : el) (h' : epost ⊑ epost') :
    wp x post epost ⊑ wp x post epost' := by
  solve_by_elim [WPMonad.wp_trans_monotone, PartialOrder.rel_refl]

theorem WPMonad.wp_econs_bot [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] (x : m α)
  (post : α → l) (epost : el) :
    wp x post ⊥ ⊑ wp x post epost := by
  solve_by_elim [WPMonad.wp_econs, bot_le]

theorem WPMonad.wp_cons_rel [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] (x : m α)
  (post post' : α → l) (epost : el) (h : post ⊑ post') {pre : l}
    (h' : pre ⊑ wp x post epost) :
    pre ⊑ wp x post' epost :=
  PartialOrder.rel_trans h' (WPMonad.wp_cons x post post' epost h)

theorem WPMonad.wp_econs_rel [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] (x : m α)
  (post : α → l) (epost epost' : el) (h : epost ⊑ epost') {pre : l}
    (h' : pre ⊑ wp x post epost) :
    pre ⊑ wp x post epost' :=
  PartialOrder.rel_trans h' (WPMonad.wp_econs x post epost epost' h)

theorem WPMonad.wp_econs_bot_rel [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] (x : m α)
  (post : α → l) (epost : el) {pre : l} (h : pre ⊑ wp x post ⊥) :
    pre ⊑ wp x post epost :=
  PartialOrder.rel_trans h (WPMonad.wp_econs_bot x post epost)

/-!
## Derived Theorems for `map` and `seq`

One direction of the derived theorems `wp_map` and `wp_seq`. The full bidirectional
equality from `Std.Do` cannot be proven with our current axioms since `wp_bind` only
gives one direction (`⊑`).
-/

theorem WPMonad.wp_map [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] (f : α → β) (x : m α) :
  ∀ post epost, wp x (fun a => post (f a)) epost ⊑ wp (f <$> x) post epost := by
  intro post epost
  rw [← bind_pure_comp]
  apply PartialOrder.rel_trans; rotate_left
  exact WPMonad.wp_trans_bind x (pure <| f ·) post epost
  apply WPMonad.wp_cons
  intro a; exact WPMonad.wp_trans_pure (f a) post epost

theorem WPMonad.wp_map' [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] (f : α → β) (x : m α) :
  ∀ post post' epost (_ : post = fun a => post' (f a)),
    wp x post epost ⊑ wp (f <$> x) post' epost := by
  intro post post' epost h
  subst h
  apply wp_map

theorem WPMonad.wp_seq [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] (f : m (α → β)) (x : m α) :
  ∀ post epost,
    wp f (fun g => wp x (fun a => post (g a)) epost) epost ⊑
      wp (f <*> x) post epost := by
  intro post epost
  rw [← bind_map]
  apply PartialOrder.rel_trans _ (WPMonad.wp_bind f (fun g => g <$> x) post epost)
  apply WPMonad.wp_cons; intro g; exact WPMonad.wp_map g x post epost

/-!
## WPMonad Instances
-/

/-- `Id` is a WPMonad with `Prop` assertions and no exceptions. -/
instance Id.instWPMonad : WPMonad Id.{u} Prop EPost.nil where
  wpTrans x := fun post _epost => post x
  wp_trans_pure _x := PartialOrder.rel_refl
  wp_trans_bind _x _f := PartialOrder.rel_refl
  wp_trans_monotone x := fun _ _ _ _ _ hpost => hpost x

/-- `Option` is a WPMonad with `Prop` assertions and a single `Prop` exception postcondition. -/
instance Option.instWPMonad : WPMonad Option.{u} Prop Prop where
  wpTrans x := fun post epost => x.elim epost post
  wp_trans_pure x := PartialOrder.rel_refl
  wp_trans_bind x f := fun post epost => by cases x <;> exact id
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    cases x with
    | none => exact hepost
    | some a => exact hpost a

@[simp, grind =]
theorem apply_pushExcept {α ε l el}
    (x : PredTrans l el (Except ε α)) (post : α → l)
    (epost : EPost.cons (ε → l) el) :
    (PredTrans.pushExcept x) post epost = x (epost.pushExcept post) epost.tail := rfl

/-- `ExceptT` lifts a `WPMonad` instance by adding an exception postcondition layer. -/
instance ExceptT.instWPMonad {l : Type v}
  [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] :
    WPMonad (ExceptT ε m) l (EPost.cons (ε → l) el) where
  wpTrans x := PredTrans.pushExcept (wp x.run)
  wp_trans_pure x := fun post epost =>
    WPMonad.wp_pure (m := m) (Except.ok x) (epost.pushExcept post) epost.tail
  wp_trans_bind x f := fun post epost => by
    simp only [apply_pushExcept, ExceptT.run_bind]
    apply PartialOrder.rel_trans _ (WPMonad.wp_bind (m := m) x ..)
    apply WPMonad.wp_cons (m := m)
    · intro r; cases r with
      | ok a => exact PartialOrder.rel_refl
      | error el =>
        exact WPMonad.wp_pure (m := m) (Except.error el) (epost.pushExcept post) epost.tail
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    change wp x.run (epost.pushExcept post) epost.tail ⊑
           wp x.run (epost'.pushExcept post') epost'.tail
    have hepost' : epost.head ⊑ epost'.head ∧ epost.tail ⊑ epost'.tail := by
      simpa [PartialOrder.rel, meet_prop_eq_and] using hepost
    let hhead := hepost'.1
    let htail := hepost'.2
    apply WPMonad.wp_cons_econs (m := m) (x := x.run)
    · intro r
      cases r with
      | ok a => exact hpost a
      | error el => exact hhead el
    · exact htail

@[simp, grind =]
theorem ExceptT.apply_wp {α ε l el}
  [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] (x : ExceptT ε m α)
  (post : α → l) (epost : EPost.cons (ε → l) el) :
    (wp x) post epost = wp x.run (epost.pushExcept post) epost.tail := by
  rw [show wp x post epost = PredTrans.pushExcept (wp x.run) post epost by rfl]
  rw [apply_pushExcept]

/-- `StateT` lifts a `WPMonad` instance by adding a state argument. -/
instance (priority := low) StateT.instWPMonad {el : Type v} {σ : Type u} {l : Type w}
  [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] :
    WPMonad (StateT σ m) (σ → l) el where
  wpTrans x := pushArg (wp <| x.run ·)
  wp_trans_pure x := fun post epost s =>
    WPMonad.wp_pure (m := m) (x, s) (fun p => post p.1 p.2) epost
  wp_trans_bind x f := fun post epost s => by
    simp only [apply_pushArg, StateT.run_bind]
    apply WPMonad.wp_bind
  wp_trans_monotone x := fun post post' epost epost' hepost hpost s => by
    apply WPMonad.wp_cons_econs (m := m) (x := x.run s)
    · intro ⟨a, s'⟩
      exact hpost a s'
    · exact hepost

@[simp, grind =]
theorem StateT.apply_wp {σ : Type u}
  [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] (x : StateT σ m α)
  (post : α → σ → l) (epost : el) (s : σ) :
    (wp x) post epost s = wp (x.run s) (fun (a, s) => post a s) epost := rfl

-- set_option trace.Meta.synthInstance true

/-
 -- CompleteLattice el

    -->

    WPMonad (ReaderT ?ρ ?m) (?ρ → ?l) el

    -->

    WPMonad (ReaderT ?ρ (ReaderT ?ρ ?m)) (?ρ → (?ρ → ?l)) el

-/

/-- `ReaderT` lifts a `WPMonad` instance by adding a reader argument. -/
instance ReaderT.instWPMonad {l : Type v}
  [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] :
    WPMonad (ReaderT ρ m) (ρ → l) el where
  wpTrans x := fun post epost r => wp (x.run r) (fun a => post a r) epost
  wp_trans_pure x := fun post epost r =>
    WPMonad.wp_pure (m := m) x (fun a => post a r) epost
  wp_trans_bind x f := fun post epost r => by
    simp only [ReaderT.run_bind]
    apply PartialOrder.rel_trans
    · apply WPMonad.wp_cons (m := m)
      intro a; exact PartialOrder.rel_refl
    · apply WPMonad.wp_bind
  wp_trans_monotone x := fun post post' epost epost' hepost hpost r => by
    apply WPMonad.wp_cons_econs (m := m) (x := x.run r)
    · intro a
      exact hpost a r
    · exact hepost

@[simp, grind =]
theorem ReaderT.apply_wp {ρ : Type u}
  [Monad m] [AssertionLang l] [ExceptAssertionLang el] [WPMonad m l el] (x : ReaderT ρ m α)
  (post : α → ρ → l) (epost : el) (r : ρ) :
    (wp x) post epost r = wp (x.run r) (fun a => post a r) epost := rfl

/-!
## Type Alias Instances

`WPMonad` instances for concrete monads that are type aliases for transformer stacks.
-/

/-- `Except ε` is a WPMonad with `Prop` assertions and a single exception postcondition. -/
instance Except.instWPMonad : WPMonad (Except ε) Prop EPost⟨ε → Prop⟩ where
  wpTrans x := fun post epost => match x with
    | .ok a => post a
    | .error el => epost.head el
  wp_trans_pure x := PartialOrder.rel_refl
  wp_trans_bind x f := fun post epost => by cases x <;> exact id
  wp_trans_monotone x := fun post post' epost epost' hepost hpost => by
    cases x with
    | ok a => exact hpost a
    | error el =>
      have hhead : epost.head ⊑ epost'.head := by
        have hepost' : epost.head ⊑ epost'.head ∧ epost.tail ⊑ epost'.tail := by
          simpa [PartialOrder.rel, meet_prop_eq_and] using hepost
        exact hepost'.1
      exact hhead el

/-- `EStateM ε σ` is a WPMonad combining state and exceptions. -/
instance EStateM.instWPMonad : WPMonad (EStateM ε σ) (σ → Prop) (ε → σ → Prop) where
  wpTrans x := fun post epost s => match x s with
    | .ok a s' => post a s'
    | .error el s' => epost el s'
  wp_trans_pure x := fun post epost s => PartialOrder.rel_refl
  wp_trans_bind x f := fun post epost s => by
    simp only [bind, EStateM.bind]
    cases (x s) <;> exact PartialOrder.rel_refl
  wp_trans_monotone x := fun post post' epost epost' hepost hpost s => by
    cases hxs : x s with
    | ok a s' =>
      simpa [hxs] using hpost a s'
    | error el s' =>
      simpa [hxs] using hepost el s'

/-!
## Adequacy Lemmas

These lemmas bridge `wp` reasoning to concrete program properties. Each one says:
if `wp prog ...` holds, then a property `P` holds of the program's result.
-/

theorem Id.of_wp_run_eq {α : Type u} {x : α} {prog : Id α}
  (h : Id.run prog = x) (P : α → Prop)
  (hwp : wp prog P EPost.nil.mk) : P x := by
  rw [← h]
  exact hwp

theorem Option.of_wp_eq {α : Type u} {x prog : Option α}
  (h : prog = x) (P : Option α → Prop)
  (hwp : wp prog (fun a => P (some a)) (P none)) : P x := by
  subst h
  cases prog with
  | none => exact hwp
  | some a => exact hwp

theorem StateM.of_wp_run_eq {x : α × σ} {prog : StateM σ α} {s : σ}
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
  | ok a => simpa only [wp] using hwp
  | error e => simpa only [wp] using hwp

theorem EStateM.of_wp_run_eq {ε σ α : Type} {x : EStateM.Result ε σ α}
  {prog : EStateM ε σ α} {s : σ}
  (h : EStateM.run prog s = x) (P : EStateM.Result ε σ α → Prop)
  (hwp : wp prog (fun a s' => P (.ok a s')) (fun e s' => P (.error e s')) s) :
    P x := by
  rw [← h]
  change P (prog s)
  cases heq : prog s with
  | ok a s' =>
    simpa [wp, WPMonad.wpTrans, heq] using hwp
  | error e s' =>
    simpa [wp, WPMonad.wpTrans, heq] using hwp

end Std.Do'
