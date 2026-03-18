/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Loom.LatticeExt
universe u v
@[expose] public section

set_option linter.missingDocs true

open Lean.Order

/-!
# Exception Postcondition Types

Heterogeneous lists of exception postconditions for monads with multiple exception layers.

An `EPost` is a type-level list that tracks postconditions for each exception type in a
monad transformer stack. For example, `ExceptT Nat (ExceptT String (StateM σ))` would use
`EPost⟨Nat → σ → Prop, String → σ → Prop⟩` to specify postconditions for both exception types.

## Overview

- `EPost.nil` is the empty exception postcondition (no exceptions).
- `EPost.cons eh et` pairs a head postcondition type `eh` with a tail `et`.
- `EPost⟨e₁, e₂, ...⟩` is notation for nested `EPost.cons`.
- `epost⟨v₁, v₂, ...⟩` is notation for constructing exception postcondition values.
-/

namespace Std.Do'

/-- The empty exception postcondition type, used when a monad has no exception layers. -/
inductive EPost.nil : Type where
  /-- The unique inhabitant of the empty exception postcondition. -/
  | mk

/-- A cons cell pairing a head exception postcondition type `eh` with a tail `et`.

For a monad with exception type `ε` over lattice `l`, the head `eh` is typically `ε → l`
and the tail `et` tracks remaining exception layers. -/
inductive EPost.cons (eh : Type u) (et : Type v) where
  /-- Construct an exception postcondition from a head and tail. -/
  | mk : eh → et → EPost.cons eh et

/-- Project the head exception postcondition from a cons cell. -/
@[simp]
def EPost.cons.head : EPost.cons eh et → eh
  | .mk head _ => head

/-- Project the tail exception postconditions from a cons cell. -/
@[simp]
def EPost.cons.tail : EPost.cons eh et → et
  | .mk _ tail => tail

/-!
## Partial Order and Complete Lattice Instances

Exception postconditions are ordered componentwise: `p ⊑ q` iff each component of `p`
is below the corresponding component of `q`.
-/

/-- The trivial partial order on `EPost.nil`: all values are equal. -/
instance : PartialOrder EPost.nil where
  rel _ _ := True
  rel_refl := trivial
  rel_trans _ _ := trivial
  rel_antisymm := fun {p q} _ _ => by cases p; cases q; rfl

/-- The trivial complete lattice on `EPost.nil`. -/
instance : CompleteLattice EPost.nil where
  has_sup _ := ⟨EPost.nil.mk, fun _ => ⟨fun _ _ _ => trivial, fun _ => trivial⟩⟩

/-- Componentwise partial order on `EPost.cons`: both head and tail must be ordered. -/
instance [PartialOrder eh] [PartialOrder et] : PartialOrder (EPost.cons eh et) where
  rel p q := (p.head ⊑ q.head) ⊓ (p.tail ⊑ q.tail)
  rel_refl := by
    intro p
    have h : p.head ⊑ p.head ∧ p.tail ⊑ p.tail := by
      exact And.intro PartialOrder.rel_refl PartialOrder.rel_refl
    simpa [meet_prop_eq_and] using h
  rel_trans := by
    intro p q r h1 h2
    have h1' : p.head ⊑ q.head ∧ p.tail ⊑ q.tail := by
      simpa [meet_prop_eq_and] using h1
    have h2' : q.head ⊑ r.head ∧ q.tail ⊑ r.tail := by
      simpa [meet_prop_eq_and] using h2
    have h : p.head ⊑ r.head ∧ p.tail ⊑ r.tail := by
      exact And.intro
        (PartialOrder.rel_trans h1'.1 h2'.1)
        (PartialOrder.rel_trans h1'.2 h2'.2)
    simpa [meet_prop_eq_and] using h
  rel_antisymm := by
    intro p q h1 h2
    have h1' : p.head ⊑ q.head ∧ p.tail ⊑ q.tail := by
      simpa [meet_prop_eq_and] using h1
    have h2' : q.head ⊑ p.head ∧ q.tail ⊑ p.tail := by
      simpa [meet_prop_eq_and] using h2
    cases p; cases q; congr 1
    · exact PartialOrder.rel_antisymm h1'.1 h2'.1
    · exact PartialOrder.rel_antisymm h1'.2 h2'.2

/-- Componentwise complete lattice on `EPost.cons`: suprema are taken componentwise. -/
instance [CompleteLattice eh] [CompleteLattice et] : CompleteLattice (EPost.cons eh et) where
  has_sup c := by
    let supHead : eh := CompleteLattice.sup (fun x => ∃ p, c p ∧ p.head = x)
    let supTail : et := CompleteLattice.sup (fun x => ∃ p, c p ∧ p.tail = x)
    refine ⟨EPost.cons.mk supHead supTail, ?_⟩
    intro q; constructor
    · intro hq p hp
      have hq' : supHead ⊑ q.head ∧ supTail ⊑ q.tail := by
        have hqMeet : (supHead ⊑ q.head) ⊓ (supTail ⊑ q.tail) := by
          simpa [PartialOrder.rel] using hq
        simpa [meet_prop_eq_and] using hqMeet
      have hpq : p.head ⊑ q.head ∧ p.tail ⊑ q.tail := by
        exact And.intro
          (PartialOrder.rel_trans (le_sup _ ⟨p, hp, rfl⟩) hq'.1)
          (PartialOrder.rel_trans (le_sup _ ⟨p, hp, rfl⟩) hq'.2)
      have hpqMeet : (p.head ⊑ q.head) ⊓ (p.tail ⊑ q.tail) := by
        simpa [meet_prop_eq_and] using hpq
      simpa [PartialOrder.rel] using hpqMeet
    · intro h
      have hq : supHead ⊑ q.head ∧ supTail ⊑ q.tail := by
        constructor
        · apply sup_le; rintro _ ⟨p, hp, rfl⟩
          have hpq : p ⊑ q := h p hp
          have hpq' : p.head ⊑ q.head ∧ p.tail ⊑ q.tail := by
            have hpqMeet : (p.head ⊑ q.head) ⊓ (p.tail ⊑ q.tail) := by
              simpa [PartialOrder.rel] using hpq
            simpa [meet_prop_eq_and] using hpqMeet
          exact hpq'.1
        · apply sup_le; rintro _ ⟨p, hp, rfl⟩
          have hpq : p ⊑ q := h p hp
          have hpq' : p.head ⊑ q.head ∧ p.tail ⊑ q.tail := by
            have hpqMeet : (p.head ⊑ q.head) ⊓ (p.tail ⊑ q.tail) := by
              simpa [PartialOrder.rel] using hpq
            simpa [meet_prop_eq_and] using hpqMeet
          exact hpq'.2
      have hqMeet : (supHead ⊑ q.head) ⊓ (supTail ⊑ q.tail) := by
        simpa [meet_prop_eq_and] using hq
      simpa [PartialOrder.rel] using hqMeet

/-!
## Ordering Lemmas
-/

/-- Construct an ordering proof for `EPost.cons` from component orderings. -/
@[grind .] theorem EPost.cons.mk_rel [PartialOrder eh] [PartialOrder et]
    {h1 h2 : eh} {t1 t2 : et} (hh : h1 ⊑ h2) (ht : t1 ⊑ t2) :
    EPost.cons.mk h1 t1 ⊑ EPost.cons.mk h2 t2 :=
  (meet_prop_eq_and _ _).mpr ⟨hh, ht⟩

/-- Extract a head ordering from an `EPost.cons` ordering. -/
@[grind .] theorem EPost.cons.rel_head [PartialOrder eh] [PartialOrder et]
    {p q : EPost.cons eh et} (h : p ⊑ q) : p.head ⊑ q.head :=
  ((meet_prop_eq_and _ _).mp h).1

/-- Extract a tail ordering from an `EPost.cons` ordering. -/
@[grind .] theorem EPost.cons.rel_tail [PartialOrder eh] [PartialOrder et]
    {p q : EPost.cons eh et} (h : p ⊑ q) : p.tail ⊑ q.tail :=
  ((meet_prop_eq_and _ _).mp h).2

/-- An `EPost.cons` value is below another if both components are below. -/
theorem EPost.cons_rel [PartialOrder e] [PartialOrder e'] (eposth : e) (epostt : e') (epost : EPost.cons e e') :
    eposth ⊑ epost.head →
    epostt ⊑ epost.tail →
    EPost.cons.mk eposth epostt ⊑ epost := by
  intro hh ht
  simp_all [PartialOrder.rel]

/-- The unique `EPost.nil` value is below any `EPost.nil` value. -/
theorem EPost.nil_rel (epost : EPost.nil) :
    EPost.nil.mk ⊑ epost := by
  simp [PartialOrder.rel]

/-!
## Notation

- `EPost⟨e₁, e₂, ...⟩` builds an exception postcondition **type** (nested `EPost.cons`).
- `epost⟨v₁, v₂, ...⟩` builds an exception postcondition **value** (nested `EPost.cons.mk`).
-/

/-- Exception postcondition type notation: `EPost⟨ε₁ → l, ε₂ → l⟩` for nested `EPost.cons`. -/
syntax "EPost⟨" term,* "⟩" : term
/-- Exception postcondition value notation: `epost⟨h₁, h₂⟩` for nested `EPost.cons.mk`. -/
syntax "epost⟨" term,* "⟩" : term

macro_rules
  | `(EPost⟨⟩) => `(EPost.nil)
  | `(EPost⟨$x⟩) => `(EPost.cons $x EPost.nil)
  | `(EPost⟨$x, $xs,*⟩) => `(EPost.cons $x EPost⟨$xs,*⟩)
  | `(epost⟨⟩) => `(EPost.nil.mk)
  | `(epost⟨$x⟩) => `(EPost.cons.mk $x EPost.nil.mk)
  | `(epost⟨$x, $xs,*⟩) => `(EPost.cons.mk $x epost⟨$xs,*⟩)

/-- Pretty-print `EPost.nil` as `EPost⟨⟩`. -/
@[app_unexpander EPost.nil] meta def unexpandEPostNil : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `(EPost⟨⟩)

/-- Pretty-print `EPost.cons` as `EPost⟨e₁, e₂, ...⟩`. -/
@[app_unexpander EPost.cons] meta def unexpandEPostCons : Lean.PrettyPrinter.Unexpander
  | `($(_) $x $xs) =>
    match xs with
    | `(EPost⟨⟩) => `(EPost⟨$x⟩)
    | `(EPost⟨$y⟩) => `(EPost⟨$x, $y⟩)
    | `(EPost⟨$y, $ys,*⟩) => `(EPost⟨$x, $y, $ys,*⟩)
    | _ => `(EPost.cons $x $xs)
  | _ => throw ()

/-- Pretty-print `EPost.nil.mk` as `epost⟨⟩`. -/
@[app_unexpander EPost.nil.mk] meta def unexpandEPostNilMk : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `(epost⟨⟩)

/-- Pretty-print `EPost.cons.mk` as `epost⟨v₁, v₂, ...⟩`. -/
@[app_unexpander EPost.cons.mk] meta def unexpandEPostConsMk : Lean.PrettyPrinter.Unexpander
  | `($(_) $x $xs) =>
    match xs with
    | `(epost⟨⟩) => `(epost⟨$x⟩)
    | `(epost⟨$y⟩) => `(epost⟨$x, $y⟩)
    | `(epost⟨$y, $ys,*⟩) => `(epost⟨$x, $y, $ys,*⟩)
    | _ => `(EPost.cons.mk $x $xs)
  | _ => throw ()

end Std.Do'
