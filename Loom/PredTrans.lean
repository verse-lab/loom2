import Loom.LatticeExt
import Loom.Post

open Lean.Order

-- universe u v w x

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

instance {ε : Type v} {l : Type w} {e : Type z} :
  MonadLift (PredTrans l e) (PredTrans l (EPost.cons (ε → l) e)) where
  monadLift x := PredTrans.pushExcept fun post epost => x (post <| .ok ·) epost

/--
Adds the ability to make assertions about a state of type `σ` to a predicate transformer with
postcondition shape `es`, resulting in a transformer over `σ → l`.
-/
def pushArg {σ : Type u} {l : Type v} {e : Type w} {α : Type z}
    (x : σ → PredTrans l e (α × σ)) : PredTrans (σ → l) e α :=
  fun post epost s => x s (fun (a, s) => post a s) epost

instance {σ : Type u} {l : Type v} {e : Type w}
  : MonadLift (PredTrans l e) (PredTrans (σ → l) e) where
  monadLift x := pushArg fun s post epost => x (fun x => post (x, s)) epost

@[simp, grind =]
theorem apply_pushArg {σ : Type u} {l : Type v} {e : Type w} {α : Type z}
    (x : σ → PredTrans l e (α × σ)) (post : α → σ → l) (epost : e) (s : σ) :
  (pushArg x) post epost s = x s (fun (a, s) => post a s) epost := rfl

instance {σ : Type u} {l : Type v} {e : Type w} : MonadLift (PredTrans l e) (PredTrans (σ → l) e) where
  monadLift x := fun post epost s => x (fun a => post a s) epost

instance (priority := high) {ε : Type u} {l : Type u} {e : Type u} : MonadLift.{u, u, u} (PredTrans l e) (PredTrans l (EPost.cons.{u, u} (ε → l) e)) where
  monadLift x := fun post epost => x post epost.tail


instance {σ : Type u} {l : Type v} {e : Type w} : MonadStateOf σ (PredTrans (σ → l) e) where
  get := fun post _epost => fun s => post s s
  set s := fun post _epost => fun _ => post ⟨⟩ s
  modifyGet f := fun post _epost => fun s => post (f s).1 (f s).2

instance {σ : Type u} {l : Type v} {e : Type w} : MonadReaderOf σ (PredTrans (σ → l) e) where
  read := fun post _epost => fun s => post s s

instance {ε : Type u} {l : Type v} {e : Type w} : MonadExceptOf ε (PredTrans l (EPost.cons (ε → l) e)) where
  throw e := fun _post epost => epost.head e
  tryCatch x handle := fun post epost => x post ⟨(handle · post epost), epost.tail⟩

instance {ε : Type u} {l : Type v} {e : Type w} {σ : Type z}
  [MonadExceptOf ε (PredTrans l e)] : MonadExceptOf ε (PredTrans (σ → l) e) where
  throw e := pushArg fun _ => throw e
  tryCatch x handle := pushArg fun s =>
    tryCatch
      (fun post epost => x (fun r s => post (r, s)) epost s)
      (fun e post epost => handle e (fun r s => post (r, s)) epost s)

instance {ε : Type u} {l : Type v} {e : Type w} {ε' : Type u}
  [MonadExceptOf ε (PredTrans l e)] :
  MonadExceptOf ε (PredTrans l (EPost.cons (ε' → l) e)) where
  throw e := PredTrans.pushExcept <| throw e
  tryCatch x handle := PredTrans.pushExcept <|
    tryCatch
      (fun post epost => x (fun a => post (.ok a)) ⟨fun e => post (.error e), epost⟩)
      (fun e post epost => handle e (fun r => post (.ok r)) ⟨fun e => post (.error e), epost⟩)
