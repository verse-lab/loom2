import Loom.WP.Basic
import Loom.Lawful.Lift

open Lean.Order Loom

variable (m : Type u₁ → Type u₂) (l : Type u₁) (e : Type u₁) [CompleteLattice l] [CompleteLattice e] [Monad m] [WPMonad m l e]


class LawfulMonadExceptOf (ε : Type u₁)
  [MonadExceptOf ε m] [MonadExceptOf ε (PredTrans l e)] where
  wp_throw (err : ε) : (throw err : PredTrans l e α) ⊑ wp (throw err : m α)
  wp_tryCatch (x : m α) (h : ε → m α) : (tryCatch (wp x) (wp <| h ·) : PredTrans l e α) ⊑ wp (tryCatch x h)

instance (ε : Type u₁) : LawfulMonadExceptOf (ExceptT ε m) l (EPost.cons (ε → l) e) ε where
  wp_throw := by
    simp [throw, throwThe, MonadExceptOf.throw]
    intro α err post epost
    unfold wp; simp [WPMonad.wpTrans]
    apply PartialOrder.rel_trans; rotate_left;
    apply WPMonad.wp_pure; rfl
  wp_tryCatch := by
    intro α x h post epost
    simp [tryCatch, tryCatchThe, MonadExceptOf.tryCatch]
    unfold EPost.cons.pushExcept; simp
    simp [ExceptT.run, ExceptT.tryCatch, ExceptT.mk]
    apply PartialOrder.rel_trans; rotate_left;
    apply WPMonad.wp_bind; apply WPMonad.wp_cons; intro r; cases r with
    | ok a =>
      simp; apply PartialOrder.rel_trans; rotate_left;
      apply WPMonad.wp_pure; simp; rfl
    | error e => rfl

instance (ε ε' : Type u₁) [MonadExceptOf ε m] [MonadExceptOf ε (PredTrans l e)] [LawfulMonadExceptOf m l e ε] :
  LawfulMonadExceptOf (ExceptT ε' m) l (EPost.cons (ε' → l) e) ε where
  wp_throw := by sorry
    -- simp [throw, throwThe, MonadExceptOf.throw]
    -- intro α err post epost
    -- unfold wp; simp [WPMonad.wpTrans]
    -- apply LawfulMonadExceptOf.wp_throw (m := m)
  wp_tryCatch := by sorry
    -- intro α x h post epost
    -- simp [tryCatch, tryCatchThe, MonadExceptOf.tryCatch]
    -- apply PartialOrder.rel_trans; rotate_left;
    -- apply LawfulMonadExceptOf.wp_tryCatch
    -- simp [tryCatch, tryCatchThe]
    -- unfold EPost.cons.pushExcept; simp
    -- apply PartialOrder.rel_of_eq;
    -- repeat' apply congr <;> try rfl
    -- { funext; congr; grind }
    -- funext; congr; grind

instance (ε σ : Type u₁) [MonadExceptOf ε m] [MonadExceptOf ε (PredTrans l e)] [LawfulMonadExceptOf m l e ε] :
  LawfulMonadExceptOf (StateT σ m) (σ → l) e ε where
  wp_throw := by sorry
  wp_tryCatch := by sorry

instance (ε ρ : Type u₁) [MonadExceptOf ε m] [MonadExceptOf ε (PredTrans l e)] [LawfulMonadExceptOf m l e ε] :
  LawfulMonadExceptOf (ReaderT ρ m) (ρ → l) e ε where
  wp_throw := by sorry
  wp_tryCatch := by sorry
