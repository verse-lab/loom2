import Loom.WP.Basic
import Loom.Lawful.Lift

open Lean.Order Loom

variable (m : Type u₁ → Type u₂) (l : Type u₂) (e : Type u₃) [CompleteLattice l] [CompleteLattice e] [Monad m] [WPMonad m l e]

class LawfulMonadStateOf (σ : Type u₁) [WPMonad m l e]
  [MonadStateOf σ m] [MonadStateOf σ (PredTrans l e)] where
  wp_get : (get : PredTrans l e σ) ⊑ wp (get : m σ)
  wp_set (s : σ) : (set s : PredTrans l e PUnit) ⊑ wp (set s : m PUnit)
  wp_modifyGet (f : σ → α × σ) : (modifyGet f : PredTrans l e α) ⊑ wp (modifyGet f : m α)

instance StateT.instLawfulMonadStateOf (σ : Type u₁) : LawfulMonadStateOf (StateT σ m) (σ → l) e σ where
  wp_get := by
    simp [get, getThe, MonadStateOf.get]
    intro post epost s
    unfold wp; simp [WPMonad.wpTrans]
    unfold StateT.get StateT.run; simp; apply PartialOrder.rel_trans; rotate_left;
    apply WPMonad.wp_pure; rfl
  wp_set := by
    simp [set, MonadStateOf.set]
    intro post epost e s
    unfold wp; simp [WPMonad.wpTrans]
    unfold StateT.set StateT.run; simp; apply PartialOrder.rel_trans; rotate_left;
    apply WPMonad.wp_pure; rfl
  wp_modifyGet := by
    simp [modifyGet, MonadStateOf.modifyGet]
    intro α post post' epost s; simp
    unfold wp StateT.modifyGet StateT.run; simp; apply PartialOrder.rel_trans; rotate_left;
    apply WPMonad.wp_pure; rfl

instance (σ : Type u₁)
  [MonadStateOf σ m] [MonadStateOf σ (PredTrans l e)] [LawfulMonadStateOf m l e σ]
  (n : Type u₁ → Type u₂) (k : Type u₂) (d : Type u₃)
  [CompleteLattice k] [CompleteLattice d] [Monad n] [WPMonad n k d]
  [MonadLift m n]
  [MonadLift (PredTrans l e) (PredTrans k d)]
  [LawfulWPMonadLift m l e n k d] :
  LawfulMonadStateOf n k d σ where
  wp_get := by
    simp [get, getThe, MonadStateOf.get]
    apply PartialOrder.rel_trans; rotate_left
    apply lift_wp_trans (l := l) (e := e)
    apply lift_monotone (m := m) (n := n)
    apply LawfulMonadStateOf.wp_get
  wp_set := by
    simp [set, MonadStateOf.set]; intro s
    apply PartialOrder.rel_trans; rotate_left
    apply lift_wp_trans (l := l) (e := e)
    apply lift_monotone (m := m) (n := n)
    apply LawfulMonadStateOf.wp_set
  wp_modifyGet := by
    simp [modifyGet, MonadStateOf.modifyGet]; intro α f
    apply PartialOrder.rel_trans; rotate_left
    apply lift_wp_trans (l := l) (e := e)
    apply lift_monotone (m := m) (n := n)
    apply LawfulMonadStateOf.wp_modifyGet


class LawfulMonadReaderOf (ρ : Type u₁) [MonadReaderOf ρ m] [MonadReaderOf ρ (PredTrans l e)] where
  wp_read : (read : PredTrans l e ρ) ⊑ wp (read : m ρ)

instance (ρ : Type u₁) : LawfulMonadReaderOf (ReaderT ρ m) (ρ → l) e ρ where
  wp_read := by
    simp [read, readThe, MonadReaderOf.read]
    intro post epost r
    unfold wp; simp [WPMonad.wpTrans]
    apply PartialOrder.rel_trans; rotate_left;
    apply WPMonad.wp_pure; rfl

instance (ρ : Type u₁)
  [MonadReaderOf ρ m] [MonadReaderOf ρ (PredTrans l e)] [LawfulMonadReaderOf m l e ρ]
  (n : Type u₁ → Type u₂') (k : Type u₂') (d : Type u₃')
  [CompleteLattice k] [CompleteLattice d] [Monad n] [WPMonad n k d]
  [MonadLift m n]
  [MonadLift (PredTrans l e) (PredTrans k d)]
  [LawfulWPMonadLiftT m l e n k d] :
  LawfulMonadReaderOf n k d ρ where
  wp_read := by
    simp [read, readThe, MonadReaderOf.read]
    apply PartialOrder.rel_trans; rotate_left
    apply lift_wp_trans (l := l) (e := e)
    apply lift_monotone (m := m) (n := n)
    apply LawfulMonadReaderOf.wp_read
