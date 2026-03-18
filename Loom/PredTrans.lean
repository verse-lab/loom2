/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Loom.LatticeExt
public import Loom.ExceptPost
universe u v w z
@[expose] public section

set_option linter.missingDocs true

open Lean.Order

/-!
# Predicate Transformers

This module defines the type `PredTrans l e α` of *predicate transformers* for weakest
precondition reasoning over monadic programs with exception postconditions.

A predicate transformer `x : PredTrans l e α` takes a normal postcondition `post : α → l`,
an exception postcondition `epost : e`, and returns a precondition of type `l`. It also
carries a proof that the transformation is monotone in both `post` and `epost`.

`PredTrans` forms a monad, so monadic programs can be interpreted by a monad morphism into
`PredTrans`; this is exactly what `WPMonad` encodes.

## Main definitions

- `PredTrans l e α` — the type of monotone predicate transformers
- `PredTrans.pushExcept` — adds an exception layer to a predicate transformer
- `pushArg` — adds a state argument to a predicate transformer
- Instances for `Monad`, `LawfulMonad`, `MonadStateOf`, `MonadExceptOf`, etc.
-/

namespace Std.Do'

/-- A monotone predicate transformer from postconditions to preconditions.

Given a return type `α`, a lattice `l` for assertions, and an exception postcondition type `e`,
`PredTrans l e α` wraps a function `(α → l) → e → l` together with a monotonicity proof:
if the postcondition and exception postcondition get weaker, the precondition gets weaker too. -/
def PredTrans (l : Type u) (e : Type v) (α : Type w) := (α → l) → e → l

/-- Partial order on predicate transformers, inherited from the function space. -/
instance [PartialOrder l] : PartialOrder (PredTrans l e α) :=
  inferInstanceAs (PartialOrder ((α → l) → e → l))

/-- Chain-complete partial order on predicate transformers, for fixed-point reasoning. -/
instance [CCPO l] : CCPO (PredTrans l e α) :=
  inferInstanceAs (CCPO ((α → l) → e → l))

/-- `Monad` instance for `PredTrans`: `pure` returns the postcondition applied to the value,
and `bind` threads the postcondition through the continuation. -/
instance instMonadPredTrans (l : Type u) (e : Type v) : Monad (PredTrans l e) where
  pure x := fun post _epost => post x
  bind x f := fun post epost => x (f · post epost) epost

/-- `PredTrans` is a lawful monad: all monad laws hold definitionally. -/
instance instLawfulMonadPredTrans (l : Type u) (e : Type v) : LawfulMonad (PredTrans l e) where
  map_const := rfl
  id_map _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := rfl

/-- Monotonicity property for a predicate transformer: if both `post` and `epost` grow,
then the resulting precondition grows. -/
def PredTrans.monotone [PartialOrder l] [PartialOrder e] (pt : PredTrans l e α) :=
  ∀ post post' epost epost', epost ⊑ epost' → post ⊑ post' → pt post epost ⊑ pt post' epost'

/-- Functorial map preserves the underlying computation, composing the postcondition with `f`. -/
@[simp] theorem PredTrans.apply_map {l : Type u} {e : Type v} {α : Type w}
    [PartialOrder l]
    (trans : PredTrans l e α) (f : α → β) (post : β → l) :
    (f <$> trans) post = trans (post ∘ f) := rfl

/-!
## Exception Handling

Definitions for pushing and lifting exception layers through predicate transformers.
-/

/-- Push an `Except ε α` result into separate normal and exception postconditions:
`ok a` uses `post a`, and `error e` uses `epost.head e`. -/
@[simp]
abbrev EPost.cons.pushExcept {α : Type u} {ε : Type v} {l : Type w} {e : Type z}
    (post : α → l) (epost : EPost.cons (ε → l) e) : Except ε α → l :=
  fun
  | .ok a => post a
  | .error e => epost.head e

/-- Adds an exception layer to a predicate transformer.

Given a transformer over `Except ε α`, produces one over `α` with an additional
exception postcondition for `ε`. The normal and error postconditions are combined
via `pushExcept`. -/
def PredTrans.pushExcept {α : Type u} {ε : Type v} {l : Type w} {e : Type z}
    (x : PredTrans l e (Except ε α)) : PredTrans l (EPost.cons (ε → l) e) α :=
  fun post epost => x (epost.pushExcept post) epost.tail

/-- Lift a predicate transformer to one with an additional exception layer,
ignoring the new exception postcondition. -/
instance {ε : Type v} {l : Type w} {e : Type z} :
    MonadLift (PredTrans l e) (PredTrans l (EPost.cons (ε → l) e)) where
  monadLift x := fun post epost => x post epost.tail

/-!
## State Handling

Definitions for adding state arguments to predicate transformers.
-/

/-- Adds a state argument to a predicate transformer.

Given a state-dependent transformer `σ → PredTrans l e (α × σ)`, produces a transformer
over `σ → l` that threads the state through postconditions. -/
def pushArg {σ : Type u} {l : Type v} {e : Type w} {α : Type z}
    (x : σ → PredTrans l e (α × σ)) : PredTrans (σ → l) e α :=
  fun post epost s => x s (fun (a, s) => post a s) epost

/-- Lift a predicate transformer to one with a state argument,
pairing the result with the original state. -/
instance {σ : Type u} {l : Type v} {e : Type w}
    : MonadLift (PredTrans l e) (PredTrans (σ → l) e) where
  monadLift x := pushArg fun s post epost => x (fun x => post (x, s)) epost

/-- Unfolding lemma for `pushArg`: applies the state-threaded transformer at state `s`. -/
@[simp, grind =]
theorem apply_pushArg {σ : Type u} {l : Type v} {e : Type w} {α : Type z}
    (x : σ → PredTrans l e (α × σ)) (post : α → σ → l) (epost : e) (s : σ) :
    (pushArg x) post epost s = x s (fun (a, s) => post a s) epost := rfl

/-- Lift a predicate transformer to one with a state argument (pointwise). -/
instance {σ : Type u} {l : Type v} {e : Type w} :
    MonadLift (PredTrans l e) (PredTrans (σ → l) e) where
  monadLift x := fun post epost s => x (fun a => post a s) epost

/-- Lift a predicate transformer to one with an additional exception layer (high priority). -/
instance (priority := high) {ε : Type u} {l : Type u} {e : Type u} :
    MonadLift (PredTrans l e) (PredTrans l (EPost.cons (ε → l) e)) where
  monadLift x := fun post epost => x post epost.tail

/-!
## Monad Instances

Standard monad class instances for `PredTrans`.
-/

/-- `MonadStateOf` instance: `get` returns the state, `set` replaces it,
`modifyGet` applies a function to the state. -/
instance {σ : Type u} {l : Type v} {e : Type w} :
    MonadStateOf σ (PredTrans (σ → l) e) where
  get := fun post _epost => fun s => post s s
  set s := fun post _epost => fun _ => post ⟨⟩ s
  modifyGet f := fun post _epost => fun s => post (f s).1 (f s).2

/-- `MonadReaderOf` instance: `read` provides the state without consuming it. -/
instance {σ : Type u} {l : Type v} {e : Type w} :
    MonadReaderOf σ (PredTrans (σ → l) e) where
  read := fun post _epost => fun s => post s s

/-- `MonadExceptOf` instance for the outermost exception layer:
`throw` invokes the head exception postcondition, `tryCatch` intercepts it. -/
instance {ε : Type u} {l : Type v} {e : Type w} :
    MonadExceptOf ε (PredTrans l (EPost.cons (ε → l) e)) where
  throw e := fun _post epost => epost.head e
  tryCatch x handle := fun post epost => x post ⟨(handle · post epost), epost.tail⟩

/-- `MonadExceptOf` instance lifted through a state layer:
delegates `throw` and `tryCatch` to the inner `PredTrans l e` instance. -/
instance {ε : Type u} {l : Type v} {e : Type w} {σ : Type z}
    [MonadExceptOf ε (PredTrans l e)] :
    MonadExceptOf ε (PredTrans (σ → l) e) where
  throw {α} x := fun post epost s =>
    throw (m := PredTrans l e) (α := α) x (post · s) epost
  tryCatch x handle := fun post epost s =>
    tryCatch (m := PredTrans l e)
      (fun post epost => x (fun r s => post (r, s)) epost s)
      (fun e post epost => handle e (fun r s => post (r, s)) epost s)
      (fun rs => post rs.1 rs.2) epost

/-- `MonadExceptOf` instance lifted through an unrelated exception layer:
delegates to the inner instance, threading the extra exception postcondition. -/
instance {ε : Type u} {l : Type v} {e : Type w} {ε' : Type u}
    [MonadExceptOf ε (PredTrans l e)] :
    MonadExceptOf ε (PredTrans l (EPost.cons (ε' → l) e)) where
  throw x := fun post epost => (throw (m := PredTrans l e) x) post epost.tail
  tryCatch x handle := fun post epost =>
    tryCatch (m := PredTrans l e)
      (fun post' epost' => x post' ⟨epost.head, epost'⟩)
      (fun e post' epost' => handle e post' ⟨epost.head, epost'⟩)
      post epost.tail

end Std.Do'
