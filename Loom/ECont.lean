import Loom.LatticeExt

open Lean.Order

/-!
# Exception Continuation Monad

The continuation monad for weakest precondition transformers.
-/

abbrev ECont (t : Type v) (e : Type w) (α : Type u) := (α → t) → e → t

instance instMonadCont (t : Type v) (e : Type w) : Monad (ECont t e) where
  pure x := fun cont _econt => cont x
  bind x f := fun cont econt => x (f · cont econt) econt

instance instLawfulMonadCont (t : Type v) (e : Type w) : LawfulMonad (ECont t e) where
  map_const := rfl
  id_map _ := rfl
  seqLeft_eq _ _ := rfl
  seqRight_eq _ _ := rfl
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := rfl

def ECont.monotone {t : Type v} {e : Type w} {α : Type u} [PartialOrder t] (wp : ECont t e α) :=
  ∀ (cont cont' : α → t), (∀ a, cont a ⊑ cont' a) → wp cont ⊑ wp cont'

def ECont.exceptMonotone {t : Type v} {e : Type w} {α : Type u} [PartialOrder e] [PartialOrder t] (wp : ECont t e α) :=
  ∀ (econt econt' : e) (cont : α → t), (econt ⊑ econt') → wp cont econt ⊑ wp cont econt'

instance monadExceptOfECont (t : Type u) (ε : Type v) : MonadExceptOf ε (ECont t (e × (ε → t))) where
  throw e := fun _cont econt => econt.2 e
  tryCatch x handle := fun cont econt => x cont (econt.1, (handle · cont econt))
