import Loom.LatticeExt
import Loom.Post

open Lean.Order

universe u v w x

/-!
# Exception Continuation Monad

The continuation monad for weakest precondition transformers.
-/

def PredTrans (t : Type u) (e : Type v) (α : Type w) := (α → t) → e → t

instance [PartialOrder t] : PartialOrder (PredTrans t e α) :=
  inferInstanceAs (PartialOrder ((α → t) → e → t))

instance [CCPO t] : CCPO (PredTrans t e α) :=
  inferInstanceAs (CCPO ((α → t) → e → t))

instance instMonadCont (t : Type u) (e : Type v) : Monad (PredTrans t e) where
  pure x := fun post _epost => post x
  bind x f := fun post epost => x (f · post epost) epost

instance instLawfulMonadCont (t : Type u) (e : Type v) : LawfulMonad (PredTrans t e) where
  map_const := rfl
  id_map _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := rfl

def PredTrans.monotone [PartialOrder l] [PartialOrder e] (pt : PredTrans l e α) :=
  ∀ post post' epost epost', post ⊑ post' → epost ⊑ epost' → pt post epost ⊑ pt post' epost'

-- instance monadExceptOfPredTrans (t : Type u) (ε : Type v) :
--     MonadExceptOf ε (PredTrans t ((ε → t) × e)) where
--   throw e := fun _post epost => epost.1 e
--   tryCatch x handle := fun post epost => x post ((handle · post epost), epost.2)

@[simp] theorem PredTrans.apply_map {l : Type u} {e : Type v} {α : Type w} [PartialOrder l]
    (trans : PredTrans l e α) (f : α → β) (post : β → l) :
  (f <$> trans) post = trans (post ∘ f) := rfl

@[simp]
abbrev EPost.cons.pushExcept {α : Type u} {ε : Type v} {l : Type w} {e : Type z}
    (post : α → l) (epost : EPost.cons (ε → l) e) : Except ε α → l :=
  fun
  | .ok a => post a
  | .error e => epost.head e

/--
Adds the ability to make assertions about exceptions of type `ε` to a predicate transformer with
postcondition on exceptions of type `es`, resulting in postcondition on exceptions of type
`(ε → l) :: es`.
-/
def PredTrans.pushExcept {α : Type u} {ε : Type v} {l : Type w} {e : Type z}
    (x : PredTrans l e (Except ε α)) : PredTrans l (EPost.cons (ε → l) e) α :=
  fun post epost => x (epost.pushExcept post) epost.tail

/--
Adds the ability to make assertions about a state of type `σ` to a predicate transformer with
postcondition shape `es`, resulting in a transformer over `σ → l`.
-/
def pushArg {σ : Type u} {l : Type v} {e : Type w} {α : Type z}
    (x : σ → PredTrans l e (α × σ)) : PredTrans (σ → l) e α :=
  fun post epost s => x s (fun (a, s) => post a s) epost

@[simp, grind =]
theorem apply_pushArg {σ : Type u} {l : Type v} {e : Type w} {α : Type z}
    (x : σ → PredTrans l e (α × σ)) (post : α → σ → l) (epost : e) (s : σ) :
  (pushArg x) post epost s = x s (fun (a, s) => post a s) epost := rfl
