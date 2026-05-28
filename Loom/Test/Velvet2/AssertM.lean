import Loom.Test.Velvet.Gadgets
import Loom.Triple.SpecLemmas
import Loom.LatticeExt

structure AssertM (α : Type u) where
  guard : Prop
  run : guard → α

attribute [grind] Lean.Order.PartialOrder.rel

abbrev AssertM.pure {α : Type u} (x : α) : AssertM α :=
  ⟨True, fun _ => x⟩

structure AssertM.Proof (p : Prop) : Type where
  proof : p

instance {p : Prop} : CoeOut (AssertM.Proof p) p where
  coe h := h.proof

def AssertM.assume (p : Prop) : AssertM (AssertM.Proof p) :=
  ⟨p, fun h => ⟨h⟩⟩

theorem AssertM.Proof.ext {p : Prop} (h₁ h₂ : AssertM.Proof p) : h₁ = h₂ := by
  cases h₁
  cases h₂
  simp

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
open Std.Do'

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

def AssertM.abort {α : Type u} : AssertM α :=
  ⟨False, False.elim⟩

instance : Nonempty (AssertM α) :=
  ⟨bottom⟩

namespace AssertM
open Std.Do'

theorem flat_rel_iff {x y : AssertM α} :
    Lean.Order.FlatOrder.rel (b := (bottom : AssertM α)) x y ↔
      x = bottom ∨ x = y := by
  constructor
  · intro h
    cases h with
    | bot => exact Or.inl rfl
    | refl => exact Or.inr rfl
  · intro h
    rcases h with rfl | rfl
    · exact Lean.Order.FlatOrder.rel.bot
    · exact Lean.Order.FlatOrder.rel.refl

theorem bind_bottom {α β : Type u} (f : α → AssertM β) :
    (bottom >>= f) = bottom := by
  apply ext
  · constructor
    · intro h
      exact h.1
    · intro h
      cases h
  · intro hx
    cases hx.1

theorem bind_eq_bottom_of_not_guard {α β : Type u} (x : AssertM α) (f : α → AssertM β)
    (hx : ¬ x.guard) :
    (x >>= f) = bottom := by
  apply ext
  · constructor
    · intro h
      exact False.elim (hx h.1)
    · intro h
      cases h
  · intro h
    exact False.elim (hx h.1)

theorem run_eq_of_eq {x y : AssertM α} (hxy : x = y)
    (hx : x.guard) (hy : y.guard) :
    x.run hx = y.run hy := by
  cases hxy
  simp

theorem bind_eq_bottom_of_guard_bottom {α β : Type u} (x : AssertM α) (f : α → AssertM β)
    (hx : x.guard) (hf : f (x.run hx) = bottom) :
    (x >>= f) = bottom := by
  apply ext
  · constructor
    · intro h
      have hxEq : x.run h.1 = x.run hx := by
        exact congrArg x.run (Subsingleton.elim h.1 hx)
      have hf' : f (x.run h.1) = bottom := by
        rw [hxEq, hf]
      have hg := h.2 h.1
      rw [hf'] at hg
      exact hg
    · intro h
      cases h
  · intro h hy
    cases hy

theorem bind_congr_of_guard {α β : Type u} (x : AssertM α) (f g : α → AssertM β)
    (hx : x.guard) (hfg : f (x.run hx) = g (x.run hx)) :
    (x >>= f) = (x >>= g) := by
  apply ext
  · constructor
    · intro h
      constructor
      · exact h.1
      · intro hy
        have hxEq : x.run hy = x.run hx := by
          exact congrArg x.run (Subsingleton.elim hy hx)
        have hfg' : f (x.run hy) = g (x.run hy) := by
          rw [hxEq, hfg]
        rw [← hfg']
        exact h.2 hy
    · intro h
      constructor
      · exact h.1
      · intro hy
        have hxEq : x.run hy = x.run hx := by
          exact congrArg x.run (Subsingleton.elim hy hx)
        have hfg' : f (x.run hy) = g (x.run hy) := by
          rw [hxEq, hfg]
        rw [hfg']
        exact h.2 hy
  · intro hf hg
    simp only [Bind.bind, AssertM.bind] at hf hg ⊢
    rcases hf with ⟨hxf, hff⟩
    rcases hg with ⟨hxg, hgg⟩
    have hxEq : hxg = hxf := Subsingleton.elim hxg hxf
    subst hxg
    have hfg' : f (x.run hxf) = g (x.run hxf) := by
      have hxEq' : x.run hxf = x.run hx := by
        exact congrArg x.run (Subsingleton.elim hxf hx)
      rw [hxEq', hfg]
    exact run_eq_of_eq hfg' (hff hxf) (hgg hxf)

end AssertM


noncomputable instance AssertM.instCCP : Lean.Order.CCPO (AssertM α) :=
  inferInstanceAs (Lean.Order.CCPO (Lean.Order.FlatOrder (bottom : AssertM α)))

instance AssertM.instMonoBind : Lean.Order.MonoBind AssertM where
  bind_mono_left := by
    intro α β a₁ a₂ f h
    rcases AssertM.flat_rel_iff.mp h with hbot | heq
    · rw [hbot, AssertM.bind_bottom]
      exact Lean.Order.FlatOrder.rel.bot
    · rw [heq]
  bind_mono_right := by
    intro α β a f₁ f₂ h
    by_cases ha : a.guard
    · rcases AssertM.flat_rel_iff.mp (h (a.run ha)) with hbot | heq
      · rw [AssertM.bind_eq_bottom_of_guard_bottom a f₁ ha hbot]
        exact Lean.Order.FlatOrder.rel.bot
      · rw [AssertM.bind_congr_of_guard a f₁ f₂ ha heq]
    · rw [AssertM.bind_eq_bottom_of_not_guard a f₁ ha]
      exact Lean.Order.FlatOrder.rel.bot

namespace AssertM
open Std.Do'

@[specialize, inline]
def loopForInLoop {β : Type} (f : Unit → β → AssertM (ForInStep β)) (b : β) : AssertM β := do
  match ← f () b with
  | ForInStep.done b => pure b
  | ForInStep.yield b => loopForInLoop f b
  partial_fixpoint

def loopForIn {β : Type} (_ : Lean.Loop) (init : β)
    (f : Unit → β → AssertM (ForInStep β)) : AssertM β :=
  loopForInLoop f init

@[instance high]
instance instForInLoop : ForIn AssertM Lean.Loop Unit where
  forIn {_β} _ b f := loopForInLoop f b

end AssertM
           
namespace Std.Do'
open Std.Do'

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

@[lspec]
theorem Spec.assertm_guard (p : Prop) {post : AssertM.Proof p → Prop} :
    Triple (p ∧ ∀ h : p, post ⟨h⟩) (AssertM.assume p) post EPost.nil.mk := by
  apply Triple.iff.mpr
  intro h
  constructor
  · exact h.1
  · intro hp
    exact h.2 hp

@[lspec]
theorem Spec.assertm_abort {α : Type} {post : α → Prop} :
    Triple False (AssertM.abort : AssertM α) post EPost.nil.mk := by
  apply Triple.iff.mpr
  intro h
  cases h

theorem Spec.assertm_guard_bind {α : Type} {pre p : Prop}
    {f : AssertM.Proof p → AssertM α} {post : α → Prop} :
    Lean.Order.PartialOrder.rel pre p →
    (∀ h : AssertM.Proof p, Triple pre (f h) post EPost.nil.mk) →
    Triple pre
      (AssertM.assume p >>= f) post EPost.nil.mk := by
  intro hguard hbody
  apply Triple.iff.mpr
  intro hpre
  unfold wp
  dsimp [AssertM.instWPMonad, Bind.bind, AssertM.bind, AssertM.assume]
  have hp : p := hguard hpre
  constructor
  · exact ⟨hp, fun hp' => (Triple.iff.mp (hbody ⟨hp'⟩) hpre).1⟩
  · intro hbind
    rcases hbind with ⟨hp', hf⟩
    exact (Triple.iff.mp (hbody ⟨hp'⟩) hpre).2 (hf hp')

@[lspec high]
theorem Spec.assertm_checked_guard_bind {α : Type} {pre p : Prop} [Decidable p]
    {f : AssertM.Proof p → AssertM α} {post : α → Prop} :
    Lean.Order.PartialOrder.rel pre p →
    (∀ h : AssertM.Proof p, Triple pre (f h) post EPost.nil.mk) →
    Triple pre
      ((if hp : p then AssertM.pure (⟨hp⟩ : AssertM.Proof p)
        else (AssertM.abort : AssertM (AssertM.Proof p))) >>= f)
      post EPost.nil.mk := by
  intro hguard hbody
  apply Triple.iff.mpr
  intro hpre
  have hp : p := hguard hpre
  by_cases hp' : p
  · simp [hp', AssertM.pure_bind]
    exact Triple.iff.mp (hbody ⟨hp'⟩) hpre
  · exact False.elim (hp' hp)

@[lspec high]
theorem Spec.assertm_guard_bind_dep {α : Type} {pre p : Prop}
    {f : p → AssertM.Proof p → AssertM α} {post : α → Prop} :
    Lean.Order.PartialOrder.rel pre p →
    (∀ hp : p, ∀ hg : AssertM.Proof p, Triple pre (f hp hg) post EPost.nil.mk) →
    Triple pre
      (AssertM.assume p >>= fun h => f h.proof h) post EPost.nil.mk := by
  intro hguard hbody
  apply Triple.iff.mpr
  intro hpre
  unfold wp
  dsimp [AssertM.instWPMonad, Bind.bind, AssertM.bind, AssertM.assume]
  have hp : p := hguard hpre
  constructor
  · exact ⟨hp, fun hp' => (Triple.iff.mp (hbody hp' ⟨hp'⟩) hpre).1⟩
  · intro hbind
    rcases hbind with ⟨hp', hf⟩
    exact (Triple.iff.mp (hbody hp' ⟨hp'⟩) hpre).2 (hf hp')

@[lspec high]
theorem Spec.dite_assertm_guard_bind {α : Type} {pre p : Prop} [Decidable p]
    {t : p → AssertM.Proof p → AssertM α} {e : ¬p → AssertM α} {post : α → Prop}
    (hthen : ∀ hp : p, ∀ hg : AssertM.Proof p, Triple pre (t hp hg) post EPost.nil.mk)
    (helse : ∀ hn : ¬p, Triple pre (e hn) post EPost.nil.mk) :
    Triple pre
      (if hp : p then AssertM.assume p >>= t hp else e hp)
      post EPost.nil.mk := by
  apply Triple.iff.mpr
  intro hpre
  by_cases hp : p
  · simp [hp]
    unfold wp
    dsimp [AssertM.instWPMonad, Bind.bind, AssertM.bind, AssertM.assume]
    constructor
    · exact ⟨hp, fun hp' => (Triple.iff.mp (hthen hp ⟨hp'⟩) hpre).1⟩
    · intro hbind
      rcases hbind with ⟨hp', hf⟩
      exact (Triple.iff.mp (hthen hp ⟨hp'⟩) hpre).2 (hf hp')
  · simp [hp]
    exact Triple.iff.mp (helse hp) hpre

end Std.Do'

namespace AssertM
open Std.Do'

theorem guard_of_triple {α : Type} {pre : Prop} {x : AssertM α}
    {post : α → Prop} (h : Triple pre x post EPost.nil.mk) (hpre : pre) :
    x.guard := by
  exact (Triple.iff.mp h hpre).1

end AssertM

namespace AssertM
open Std.Do'

theorem repeat_inv_total {β : Type} (f : Unit → β → AssertM (ForInStep β))
    (inv : β → Prop) (doneWith : β → Prop) (measure : β → Nat)
    (init : β)
    (hstep : ∀ b, Triple (inv b) (f () b)
      (fun | ForInStep.yield b' => inv b' ∧ measure b' < measure b
           | ForInStep.done b' => inv b' ∧ doneWith b') EPost.nil.mk) :
    Triple (inv init) (loopForInLoop f init) (fun b => inv b ∧ doneWith b) EPost.nil.mk := by
  apply Triple.iff.mpr
  intro hinit
  unfold wp
  dsimp [AssertM.instWPMonad]
  let motive : Nat → Prop := fun n => ∀ b, measure b = n → inv b →
    (loopForInLoop f b).guard ∧
      ∀ h : (loopForInLoop f b).guard,
        inv ((loopForInLoop f b).run h) ∧ doneWith ((loopForInLoop f b).run h)
  have hAll : motive (measure init) := by
    exact Nat.strongRecOn (motive := motive) (measure init) (by
      intro n ih b hb hInv
      rw [loopForInLoop.eq_def]
      dsimp only [Bind.bind, AssertM.bind, AssertM.pure]
      have hwp : (f () b).guard ∧ ∀ h : (f () b).guard,
          (match (f () b).run h with
          | ForInStep.yield b' => inv b' ∧ measure b' < measure b
          | ForInStep.done b' => inv b' ∧ doneWith b') := by
        exact Triple.iff.mp (hstep b) hInv
      constructor
      · exact ⟨hwp.1, by
          intro hf
          have hpost := hwp.2 hf
          cases hs : (f () b).run hf with
          | done _ =>
              exact True.intro
          | yield b' =>
              simp only [hs] at hpost
              have hlt : measure b' < n := by
                exact hb ▸ hpost.2
              have hloop := ih (measure b') hlt b' rfl hpost.1
              exact hloop.1⟩
      · intro hloop
        rcases hloop with ⟨hf, hrest⟩
        have hpost := hwp.2 hf
        cases hs : (f () b).run hf with
        | done _ =>
            simp only [hs] at hpost
            simp only [hs]
            exact hpost
        | yield b' =>
            simp only [hs] at hpost
            simp only [hs]
            have hlt : measure b' < n := by
              exact hb ▸ hpost.2
            have hloop' := ih (measure b') hlt b' rfl hpost.1
            have hbranch := hrest hf
            simp only [hs] at hbranch
            exact hloop'.2 hbranch)
  exact hAll init rfl hinit

end AssertM

namespace Std.Do'
open Std.Do'

@[lspec high]
theorem Spec.forIn_loop_assertm_total_guarded
    {β : Type} {init : β} {cond : β → Prop} [DecidablePred cond]
    {body : (b : β) → cond b → AssertM.Proof (cond b) → AssertM (ForInStep β)}
    {inv : β → Prop} {measure : β → Nat} {doneWith : β → Prop}
    (done : ∀ b, ¬ cond b → Lean.Order.PartialOrder.rel (inv b) (doneWith b))
    (step : ∀ b, ∀ hc : cond b, ∀ hg : AssertM.Proof (cond b),
      Triple (inv b) (body b hc hg)
        (fun | ForInStep.yield b' => inv b' ∧ measure b' < measure b
             | ForInStep.done b' => inv b' ∧ doneWith b') EPost.nil.mk) :
    Triple (inv init) (forIn Lean.Loop.mk init fun _ b => do
      invariantGadget (inv b)
      decreasingGadget (measure b)
      onDoneGadget (doneWith b)
      if hc : cond b then
        let hg ← AssertM.assume (cond b)
        body b hc hg
      else
        AssertM.pure (ForInStep.done b))
      (fun b => inv b ∧ doneWith b) EPost.nil.mk := by
  apply AssertM.repeat_inv_total (init := init) (measure := measure)
  intro b
  show Triple (inv b)
    (invariantGadget (inv b) >>= fun _ =>
      decreasingGadget (measure b) >>= fun _ =>
        onDoneGadget (doneWith b) >>= fun _ =>
          if hc : cond b then
            AssertM.assume (cond b) >>= fun hg => body b hc hg
          else
            AssertM.pure (ForInStep.done b)) _ _
  unfold invariantGadget decreasingGadget onDoneGadget
  by_cases hc : cond b
  · simp [hc]
    apply Spec.assertm_guard_bind
    · intro _
      exact hc
    · intro hg
      exact step b hc hg
  · simp [hc]
    apply Triple.iff.mpr
    intro hInv
    constructor
    · exact True.intro
    · intro _
      exact ⟨hInv, done b hc hInv⟩

@[lspec high]
theorem Spec.forIn_loop_assertm_total_guarded_by
    {β : Type} {init : β} {cond guard : β → Prop} [DecidablePred cond]
    {body : (b : β) → cond b → AssertM.Proof (guard b) → AssertM (ForInStep β)}
    {inv : β → Prop} {measure : β → Nat} {doneWith : β → Prop}
    (done : ∀ b, ¬ cond b → Lean.Order.PartialOrder.rel (inv b) (doneWith b))
    (guard_ok : ∀ b, cond b → Lean.Order.PartialOrder.rel (inv b) (guard b))
    (step : ∀ b, ∀ hc : cond b, ∀ hg : AssertM.Proof (guard b),
      Triple (inv b) (body b hc hg)
        (fun | ForInStep.yield b' => inv b' ∧ measure b' < measure b
             | ForInStep.done b' => inv b' ∧ doneWith b') EPost.nil.mk) :
    Triple (inv init) (forIn Lean.Loop.mk init fun _ b => do
      invariantGadget (inv b)
      decreasingGadget (measure b)
      onDoneGadget (doneWith b)
      if hc : cond b then
        let hg ← AssertM.assume (guard b)
        body b hc hg
      else
        AssertM.pure (ForInStep.done b))
      (fun b => inv b ∧ doneWith b) EPost.nil.mk := by
  apply AssertM.repeat_inv_total (init := init) (measure := measure)
  intro b
  show Triple (inv b)
    (invariantGadget (inv b) >>= fun _ =>
      decreasingGadget (measure b) >>= fun _ =>
        onDoneGadget (doneWith b) >>= fun _ =>
          if hc : cond b then
            AssertM.assume (guard b) >>= fun hg => body b hc hg
          else
            AssertM.pure (ForInStep.done b)) _ _
  unfold invariantGadget decreasingGadget onDoneGadget
  by_cases hc : cond b
  · simp [hc]
    apply Spec.assertm_guard_bind
    · exact guard_ok b hc
    · intro hg
      exact step b hc hg
  · simp [hc]
    apply Triple.iff.mpr
    intro hInv
    constructor
    · exact True.intro
    · intro _
      exact ⟨hInv, done b hc hInv⟩

@[lspec]
theorem Spec.forIn_loop_assertm_total
    {β : Type} {init : β} {f : Unit → β → AssertM (ForInStep β)}
    {inv : β → Prop} {measure : β → Nat} {doneWith : β → Prop}
    (step : ∀ b, Triple (inv b) (f () b)
      (fun | ForInStep.yield b' => inv b' ∧ measure b' < measure b
           | ForInStep.done b' => inv b' ∧ doneWith b') EPost.nil.mk) :
    Triple (inv init) (forIn Lean.Loop.mk init fun u b => do
      invariantGadget (inv b)
      decreasingGadget (measure b)
      onDoneGadget (doneWith b)
      f u b)
      (fun b => inv b ∧ doneWith b) EPost.nil.mk := by
  apply AssertM.repeat_inv_total (init := init) (measure := measure)
  intro b
  show Triple (inv b)
    (invariantGadget (inv b) >>= fun _ =>
      decreasingGadget (measure b) >>= fun _ =>
        onDoneGadget (doneWith b) >>= fun _ => f () b) _ _
  unfold invariantGadget decreasingGadget onDoneGadget
  simp
  exact step b
    

end Std.Do'
