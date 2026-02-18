import Loom.LatticeExt
import Loom.EPost

open Lean.Order

universe u v w x

/-!
# Exception Continuation Monad

The continuation monad for weakest precondition transformers.
-/

abbrev PredTrans (t : Sort u) (es : List (Type v)) (α : Sort w) := (α → t) → EPost es → t

instance instMonadCont (t : Type u) (es : List (Type v)) : Monad (PredTrans t es) where
  pure x := fun cont _ => cont x
  bind x f := fun cont epost => x (f · cont epost) epost

instance instLawfulMonadCont (t : Type u) (es : List (Type v)) : LawfulMonad (PredTrans t es) where
  map_const := rfl
  id_map _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := rfl

def PredTrans.monotone {t : Type u} {es : List (Type v)} {α : Type w} [PartialOrder t] (wp : PredTrans t es α) :=
  ∀ (post post' : α → t), (∀ a, post a ⊑ post' a) → wp post ⊑ wp post'

def PredTrans.exceptMonotone {t : Type u} {es : List (Type v)} {α : Type w} [PartialOrder t] (wp : PredTrans t es α) :=
  ∀ (epost epost' : EPost es) (post : α → t), wp post epost ⊑ wp post epost'

instance monadExceptOfPredTrans (t : Type u) (ε : Type v) {es : List (Type (max u v))} :
    MonadExceptOf ε (PredTrans t ((ε → t) :: es)) where
  throw e := fun _post epost => epost.head e
  tryCatch x handle := fun post epost => x post (EPost.cons (handle · post epost) epost.tail)

@[simp] theorem PredTrans.apply_map {t : Type u} {es : List (Type v)} {α : Type w} [PartialOrder t]
    (trans : PredTrans t es α) (f : α → β) (post : β → t) (epost : EPost es) :
  (f <$> trans) post epost = trans (fun a => post (f a)) epost := rfl

abbrev pushExcept.post {α : Type u} {ε : Type v} {l : Type w} {es : List (Type (max v w))}
    (post : α → l) (epost : EPost ((ε → l) :: es)) : Except ε α → l :=
  fun
  | .ok a => post a
  | .error e => epost.head e

/--
Adds the ability to make assertions about exceptions of type `ε` to a predicate transformer with
postcondition on exceptions of type `es`, resulting in postcondition on exceptions of type
`(ε → l) :: es`.
-/
def pushExcept {α : Type u} {ε : Type v} {l : Type w} {es : List (Type (max v w))}
    (x : PredTrans l es (Except ε α)) : PredTrans l ((ε → l) :: es) α :=
  fun post epost => x (pushExcept.post post epost) epost.tail

/--
Adds the ability to make assertions about a state of type `σ` to a predicate transformer with
postcondition shape `es`, resulting in a transformer over `σ → l`.
-/
def pushArg {σ : Type u} {l : Type v} {es : List (Type w)} {α : Type x}
    (x : σ → PredTrans l es (α × σ)) : PredTrans (σ → l) es α :=
  fun post epost s => x s (fun (a, s) => post a s) epost

@[simp, grind =]
theorem apply_pushArg {σ : Type u} {l : Type v} {es : List (Type w)} {α : Type x}
    (x : σ → PredTrans l es (α × σ)) (post : α → σ → l) (epost : EPost es) (s : σ) :
  (pushArg x) post epost s = x s (fun (a, s) => post a s) epost := rfl
