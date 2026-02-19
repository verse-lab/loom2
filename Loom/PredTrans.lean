import Loom.LatticeExt

open Lean.Order

universe u v w x

/-!
# Exception Continuation Monad

The continuation monad for weakest precondition transformers.
-/

abbrev PredTrans (t : Sort u) (e : Type v) (α : Sort w) := (α → t) → e → t

instance instMonadCont (t : Type u) (e : Type v) : Monad (PredTrans t e) where
  pure x := fun cont _ => cont x
  bind x f := fun cont epost => x (f · cont epost) epost

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

def PredTrans.monotone {t : Type u} {e : Type v} {α : Type w} [PartialOrder t] (wp : PredTrans t e α) :=
  ∀ (post post' : α → t), (∀ a, post a ⊑ post' a) → wp post ⊑ wp post'

def PredTrans.exceptMonotone {t : Type u} {e : Type v} {α : Type w} [PartialOrder t] (wp : PredTrans t e α) :=
  ∀ (epost epost' : e) (post : α → t), wp post epost ⊑ wp post epost'

instance monadExceptOfPredTrans (t : Type u) (ε : Type v) :
    MonadExceptOf ε (PredTrans t ((ε → t) × e)) where
  throw e := fun _post epost => epost.1 e
  tryCatch x handle := fun post epost => x post ((handle · post epost), epost.2)

@[simp] theorem PredTrans.apply_map {t : Type u} {e : Type v} {α : Type w} [PartialOrder t]
    (trans : PredTrans t e α) (f : α → β) (post : β → t) (epost : e) :
  (f <$> trans) post epost = trans (fun a => post (f a)) epost := rfl

abbrev pushExcept.post {α : Type u} {ε : Type v} {l : Type w} {e : Type z}
    (post : α → l) (epost : (ε → l) × e) : Except ε α → l :=
  fun
  | .ok a => post a
  | .error e => epost.1 e

/--
Adds the ability to make assertions about exceptions of type `ε` to a predicate transformer with
postcondition on exceptions of type `es`, resulting in postcondition on exceptions of type
`(ε → l) :: es`.
-/
def pushExcept {α : Type u} {ε : Type v} {l : Type w} {e : Type z}
    (x : PredTrans l e (Except ε α)) : PredTrans l ((ε → l) × e) α :=
  fun post epost => x (pushExcept.post post epost) epost.2

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
