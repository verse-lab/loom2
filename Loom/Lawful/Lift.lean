import Loom.WP.Basic
open Lean.Order Loom

section


section MonadLift

class LawfulWPMonadLift
    (m : semiOutParam (Type u → Type v)) (l : semiOutParam (Type w)) (e : semiOutParam (Type z))
    (n : Type u → Type v') (k : Type w') (d : Type z')
    [Monad m] [WPMonad m l e]
    [Monad n] [WPMonad n k d]
    [inst : MonadLift m n] [inst' : MonadLift (PredTrans l e) (PredTrans k d)] : Prop where
  /-- Lifting preserves `wp` -/
  lift_wp_trans {α : Type u} (x : m α) : inst'.monadLift (wpTrans x) ⊑ wpTrans (inst.monadLift x)
  /-- Lifting is monotone -/
  lift_monotone {α : Type u} (x y : PredTrans l e α) :
    x ⊑ y → inst'.monadLift x ⊑ inst'.monadLift y


class LawfulWPMonadLiftT
    (m : Type u → Type v) (l : Type w) (e : Type z)
    (n : Type u → Type v') (k : Type w') (d : Type z')
    [Monad m] [WPMonad m l e]
    [Monad n] [WPMonad n k d]
    [inst : MonadLiftT m n] [inst' : MonadLiftT (PredTrans l e) (PredTrans k d)] : Prop where
  /-- Lifting preserves `wp` -/
  lift_wp_trans {α : Type u} (x : m α) : inst'.monadLift (wpTrans x) ⊑ wpTrans (inst.monadLift x)
  /-- Lifting is monotone -/
  lift_monotone {α : Type u} (x y : PredTrans l e α) :
    x ⊑ y → inst'.monadLift x ⊑ inst'.monadLift y

export LawfulWPMonadLiftT (lift_wp_trans lift_monotone)

instance (m : Type u → Type v) (l : Type w) (e : Type z) (σ : Type u)
  [Monad m] [WPMonad m l e] :
  LawfulWPMonadLift m l e (StateT σ m) (σ → l) e where
  lift_wp_trans x := fun post epost s => by
    simp only [MonadLift.monadLift]
    apply PartialOrder.rel_trans; rotate_left; apply WPMonad.wp_bind
    apply WPMonad.wp_cons (m := m); intro a
    simpa using
      (WPMonad.wp_pure (m := m) (x := (a, s))
        (post := fun x => post x.fst x.snd) (epost := epost))
  lift_monotone _ _ h := fun post epost s => h (fun a => post a s) epost

instance (m : Type u → Type v) (l : Type w) (e : Type z) (ρ : Type u)
  [Monad m] [WPMonad m l e] :
  LawfulWPMonadLift m l e (ReaderT ρ m) (ρ → l) e where
  lift_wp_trans _x := fun _post _epost _r => PartialOrder.rel_refl
  lift_monotone _ _ h := fun post epost r => h (fun a => post a r) epost

instance (m : Type u → Type v) (l : Type w) (e : Type z) (ε : Type u)
  [Monad m] [WPMonad m l e] :
  LawfulWPMonadLift m l e (ExceptT ε m) l (EPost.cons (ε → l) e) where
  lift_wp_trans x := fun post epost => by
    simp only [MonadLift.monadLift, ExceptT.lift, ExceptT.mk]
    apply PartialOrder.rel_trans; rotate_left
    · exact WPMonad.wp_map (m := m) Except.ok x _ _
    · exact PartialOrder.rel_refl
  lift_monotone _ _ h := fun post epost => h post epost.tail

variable {m : Type u → Type v} {n : Type u → Type w} {o : Type u → Type x}


-- analogue of instLawfulMonadLiftT (reflexive)
instance
    {l : Type w'} {e : Type z'}
    [Monad m] [WPMonad m l e] :
    LawfulWPMonadLiftT m l e m l e where
  lift_wp_trans _x := fun _post _epost => PartialOrder.rel_refl
  lift_monotone _ _ h := h

-- analogue of instLawfulMonadLiftTOfLawfulMonadLift (transitive)
instance
    {l : Type w'} {e : Type z'} {k : Type w''} {d : Type z''} {p : Type w'''} {c : Type z'''}
    [Monad m] [WPMonad m l e]
    [Monad n] [WPMonad n k d]
    [Monad o] [WPMonad o p c]
    [MonadLiftT m n] [MonadLiftT (PredTrans l e) (PredTrans k d)]
    [MonadLift n o] [MonadLift (PredTrans k d) (PredTrans p c)]
    [LawfulWPMonadLift n k d o p c] [LawfulWPMonadLiftT m l e n k d] :
    LawfulWPMonadLiftT m l e o p c where
  lift_wp_trans x := by
    apply PartialOrder.rel_trans
    · apply LawfulWPMonadLift.lift_monotone (m := n) (n := o)
      exact LawfulWPMonadLiftT.lift_wp_trans (n := n) x
    · exact LawfulWPMonadLift.lift_wp_trans (monadLift x : n _)
  lift_monotone x y h := by
    apply LawfulWPMonadLift.lift_monotone (m := n) (n := o)
    exact LawfulWPMonadLiftT.lift_monotone (m := m) (n := n) (l := l) (e := e) (k := k) (d := d) x y h


end MonadLift
