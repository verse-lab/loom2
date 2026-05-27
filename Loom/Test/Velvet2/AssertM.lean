import Loom.WP.Basic

structure AssertM (α : Type u) where
  guard : Prop
  run : guard → α

abbrev AssertM.pure {α : Type u} (x : α) : AssertM α :=
  ⟨True, fun _ => x⟩

abbrev AssertM.bind {α β : Type u} (x : AssertM α) (f : α → AssertM β) : AssertM β :=
  ⟨x.guard ∧ ∀ xGuard : x.guard, (f (x.run xGuard)).guard,
    fun ⟨xGuard, fGuard⟩ => (f (x.run xGuard)).run <| fGuard xGuard⟩

instance : Pure AssertM where
  pure := AssertM.pure

instance : Bind AssertM where
  bind := AssertM.bind

instance : Monad AssertM where


theorem AssertM.ext {x y : AssertM α}
    (hguard : x.guard ↔ y.guard)
    (hrun : ∀ (hx : x.guard) (hy : y.guard), x.run hx = y.run hy) :
    x = y := by
  cases x with
  | mk xGuard xRun =>
    cases y with
    | mk yGuard yRun =>
      simp at hguard hrun
      have hEq : xGuard = yGuard := propext hguard
      subst yGuard
      simp
      funext h
      exact hrun h h

namespace AssertM

@[simp]
theorem bind_pure (x : AssertM α) : x >>= pure = x := by
  apply AssertM.ext
  · constructor <;> (intro h; simp [Bind.bind] at h ⊢ ; assumption)
  · intro hx hy
    simp only [Bind.bind, AssertM.bind, AssertM.pure] at hx
    rcases hx with ⟨hx, hxImpTrue⟩
    simp only [Bind.bind]

theorem id_map (x : AssertM α) : id <$> x = x := by
  unfold Functor.map
  exact AssertM.bind_pure x

@[simp]
theorem pure_bind (x : α) (f : α → AssertM β) : pure x >>= f = f x := by
  apply AssertM.ext
  · constructor <;> (intro h; simp [Bind.bind] at h ⊢; assumption )
  · intro hx hy
    simp only [Bind.bind, AssertM.bind, AssertM.pure] at hx ⊢
    rcases hx with ⟨hx, hxImpTrue⟩
    simp 

@[simp]
theorem bind_assoc (x : AssertM α) (f : α → AssertM β) (g : β → AssertM γ) :
    x >>= f >>= g = x >>= fun x => f x >>= g := by
  apply AssertM.ext
  · constructor
    · intro h
      rcases h with ⟨xfGuard, gGuard⟩
      exact ⟨xfGuard.1, fun hx => ⟨xfGuard.2 hx,
        fun hf => gGuard ⟨hx, fun _ => hf⟩⟩⟩
    · intro h
      rcases h with ⟨hx, fgGuard⟩
      exact ⟨⟨hx, fun hx' => (fgGuard hx').1⟩,
        fun hxf => by
          simp only [Bind.bind, AssertM.bind]
          rcases hxf with ⟨hx', hf⟩
          exact (fgGuard hx').2 (hf hx')⟩
  · intro hx hy
    simp only [Bind.bind, AssertM.bind] at hx hy ⊢
    rcases hx with ⟨hxf, hg⟩
    rcases hxf with ⟨hx', hf⟩
    rcases hy with ⟨hyx, hfg⟩
    have hyx_eq : hyx = hx' := Subsingleton.elim hyx hx'
    subst hyx
    rcases hfg_h : hfg hx' with ⟨hf', hg'⟩
    simp
    have hrun :
        (f (x.run hx')).run (hf hx') = (f (x.run hx')).run hf' := by
      simp
    cases hrun
    rw [hfg_h]

end AssertM

instance instLawfulAssertM : LawfulMonad AssertM := by
  refine LawfulMonad.mk' AssertM ?_ ?_ ?_
  · intro α x
    exact AssertM.id_map x
  · intro α β x f
    exact AssertM.pure_bind x f
  · intro α β γ x f g
    exact AssertM.bind_assoc x f g

def bottom {α : Type u} : AssertM α :=
  ⟨False, False.elim⟩

instance : Nonempty (AssertM α) :=
  ⟨bottom⟩


noncomputable instance AssertM.instCCP : Lean.Order.CCPO (AssertM α) :=
  inferInstanceAs (Lean.Order.CCPO (Lean.Order.FlatOrder (bottom : AssertM α)))
           
open Std.Do'

#check Lean.Order.PartialOrder.rel

instance AssertM.instWPMonad : WPMonad AssertM Prop EPost.nil where
  wpTrans x := ⟨fun post _epost =>
    x.guard ∧ ∀ xGuard : x.guard, post (x.run xGuard)⟩
  wp_trans_pure x := by
    intro post epost hpost
    simp
    constructor <;> try intros; trivial
  wp_trans_bind := by
    intro α β x f post epost h
    rcases h with ⟨hx, hpost⟩
    constructor
    · exact ⟨hx, fun hx => (hpost hx).1⟩
    · intro hbind
      rcases hbind with ⟨hx', hf⟩
      exact (hpost hx').2 (hf hx')
  wp_trans_monotone := by
    intro α x post post' epost epost' _hepost hpost h
    rcases h with ⟨hx, hrun⟩
    exact ⟨hx, fun hx => hpost (x.run hx) (hrun hx)⟩
    
