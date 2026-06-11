import Loom.Triple.Basic
import Loom.WP.Lemmas
import Loom.Frame
import Loom.Ghost

open Lean.Order Std.Do'

namespace BasicRepr
abbrev Credit := Nat

abbrev WithCredit (Pred : Type u) := Credit → Pred

structure CreditT (m : Type u → Type v) (α : Type u) where
  run : Credit → m (α × Credit)

namespace CreditT

-- variable {α β : Type u}

@[ext] theorem ext {m : Type u → Type v} {α : Type u} {x y : CreditT m α}
    (h : ∀ c, x.run c = y.run c) : x = y := by
  cases x
  cases y
  congr
  funext c
  exact h c

protected def map [Monad m] (f : α → β) (x : CreditT m α) : CreditT m β :=
  ⟨StateT.map f x.run⟩

protected def pure [Monad m] (x : α) : CreditT m α :=
  ⟨StateT.pure x⟩

protected def bind [Monad m] (x : CreditT m α) (f : α → CreditT m β) : CreditT m β :=
  ⟨StateT.bind x.run fun a => (f a).run⟩

instance [Monad m] : Monad (CreditT m) where
  map := CreditT.map
  pure := CreditT.pure
  bind := CreditT.bind

-- Clearly the worst possible code generated.
/--
trace: [Compiler.result] size: 5
    def BasicRepr.CreditT.CreditT.tick._redArg._lam_0 toPure @&c : tobj :=
      let _x.1 := ctor_0[PUnit.unit];
      let _x.2 := 1;
      let _x.3 := Nat.add c _x.2;
      let _x.4 := ctor_0[Prod.mk] _x.1 _x.3;
      let _x.5 := toPure ◾ _x.4;
      return _x.5
[Compiler.result] size: 2
    def BasicRepr.CreditT.CreditT.tick._redArg._lam_0._boxed toPure c : tobj :=
      let res := BasicRepr.CreditT.CreditT.tick._redArg._lam_0 toPure c;
      dec c;
      return res
[Compiler.result] size: 7
    def BasicRepr.CreditT.CreditT.tick._redArg inst.1 : tobj :=
      let toApplicative := oproj[0] inst.1;
      inc[ref] toApplicative;
      dec[ref] inst.1;
      let toPure := oproj[1] toApplicative;
      inc toPure;
      dec[ref] toApplicative;
      let _f.2 := pap BasicRepr.CreditT.CreditT.tick._redArg._lam_0._boxed toPure;
      return _f.2
[Compiler.result] size: 1
    def BasicRepr.CreditT.CreditT.tick m inst.1 : tobj :=
      let _x.2 := BasicRepr.CreditT.CreditT.tick._redArg inst.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.result true in
def CreditT.tick [Monad m] : CreditT m Unit :=
  ⟨fun c => pure ((), c + 1)⟩


def linearSearchArrayIdx? [Monad m] (p : α → Bool) (xs : Array α) : CreditT m (Option Nat) :=
  ⟨fun c =>
    let rec loop (i c : Nat) : Option Nat × Nat :=
      if h : i < xs.size then
        let (_, c) := (CreditT.tick (m := Id)).run c
        if p xs[i] then
          (some i, c)
        else
          loop (i + 1) c
      else
        (none, c)
    pure (loop 0 c)⟩



instance [Monad m] [LawfulMonad m] : LawfulMonad (CreditT m) :=
  LawfulMonad.mk' (CreditT m)
    (id_map := by
      intro α x
      ext c
      simp [Functor.map, CreditT.map, StateT.map])
    (pure_bind := by
      intro α β x f
      ext c
      simp [Bind.bind, Pure.pure, CreditT.bind, CreditT.pure, StateT.bind, StateT.pure])
    (bind_assoc := by
      intro α β γ x f g
      ext c
      simp [Bind.bind, CreditT.bind, StateT.bind])
    (bind_pure_comp := by
      intro α β f x
      ext c
      simp [Bind.bind, Pure.pure, Functor.map, CreditT.bind, CreditT.map, CreditT.pure,
        StateT.bind, StateT.map, StateT.pure])

end CreditT

-- variable {m : Type u → Type v} {Pred : Type u} {EPred : Type u}

noncomputable instance [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred] :
  WPMonad (CreditT m) (WithCredit Pred) EPred where
  wpTrans {α} x := ⟨fun post epost crd =>
    ⨅ crdFrame,
       wp (x.run (crd + crdFrame)) (fun ⟨ret, crd'⟩ => ⌜ crd' ≥ crdFrame ⌝ ⊓ post ret (crd' - crdFrame)) epost⟩
  wp_trans_pure x := by
    intro post epost crd
    apply le_iInf
    intro crdFrame
    apply PartialOrder.rel_trans
    · exact le_meet (post x crd) (⌜crd + crdFrame ≥ crdFrame⌝) (post x (crd + crdFrame - crdFrame))
        (le_pure _ _ (Nat.le_add_left crdFrame crd))
        (by
          have hsub : crd + crdFrame - crdFrame = crd := Nat.add_sub_cancel crd crdFrame
          rw [hsub])
    · exact WPMonad.wp_pure (m := m) (x, crd + crdFrame)
        (fun ⟨ret, crd'⟩ => ⌜crd' ≥ crdFrame⌝ ⊓ post ret (crd' - crdFrame)) epost
  wp_trans_bind x f := by
    intro post epost crd
    apply le_iInf
    intro crdFrame
    apply PartialOrder.rel_trans (iInf_le _ crdFrame)
    apply PartialOrder.rel_trans
    · apply WPMonad.wp_consequence (m := m) (x := x.run (crd + crdFrame))
      intro ret
      rw [pure_intro_r]
      intro hcrd
      apply PartialOrder.rel_trans (iInf_le _ crdFrame)
      have hrun : ret.2 - crdFrame + crdFrame = ret.2 := Nat.sub_add_cancel hcrd
      rw [hrun]
    · simpa [Bind.bind, CreditT.bind, StateT.bind] using
        (WPMonad.wp_bind (m := m) (x := x.run (crd + crdFrame))
          (f := fun ret => (f ret.1).run ret.2)
          (post := fun ⟨ret, crd'⟩ => ⌜crd' ≥ crdFrame⌝ ⊓ post ret (crd' - crdFrame))
          epost)
  wp_trans_monotone x := by
    intro post post' epost epost' hepost hpost crd
    apply le_iInf
    intro crdFrame
    apply PartialOrder.rel_trans (iInf_le _ crdFrame)
    apply WPMonad.wp_consequence_econs (m := m) (x := x.run (crd + crdFrame))
    · intro ret
      apply le_meet
      · exact meet_le_left _ _
      · exact PartialOrder.rel_trans (meet_le_right _ _) (hpost ret.1 (ret.2 - crdFrame))
    · exact hepost

abbrev cProp := WithCredit Prop

noncomputable def cStar [CompleteLattice Pred]
    (H1 H2 : WithCredit Pred) : WithCredit Pred :=
  fun x => iSup fun x1 => ⌜x1 ≤ x⌝ ⊓ (H1 x1 ⊓ H2 (x - x1))

infixl:65 " ∗ᶜ " => cStar

noncomputable def cStarValue [CompleteLattice Pred]
    (H1 H2 : WithCredit Pred) (val : Credit) : WithCredit Pred :=
  fun x => ⌜val ≤ x⌝ ⊓ (H1 val ⊓ H2 (x - val))

noncomputable def cStarQ [CompleteLattice Pred]
    (H1 : α → WithCredit Pred) (H2 : WithCredit Pred): α → WithCredit Pred :=
  fun a x => cStar (H1 a) H2 x

noncomputable def cPure [CompleteLattice Pred] (h : Prop) : WithCredit Pred :=
  fun x => ⌜x = 0 ∧ h⌝

noncomputable def cCredit [CompleteLattice Pred] (H : Credit → Prop) : WithCredit Pred :=
  fun x => ⌜H x⌝

notation:max "⌜" H "⌝ᶜ" => cCredit H

noncomputable def cVal [CompleteLattice Pred] (x : Int) : WithCredit Pred :=
  fun x₁ => ⌜(x₁ : Int) ≤ x⌝

def cImpl [CompleteLattice Pred] (H1 H2 : WithCredit Pred) : Prop :=
  H1 ⊑ H2

noncomputable def cEq [CompleteLattice Pred] (x : Int) : WithCredit Pred :=
  fun x₁ => ⌜x = (x₁ : Int)⌝

noncomputable def cWand' [CompleteLattice Pred]
    (H1 H2 : WithCredit Pred) : WithCredit Pred :=
  fun x => iInf fun x1 => H1 x1 ⇨ H2 (x + x1)

infixr:60 " -∗ᶜ " => cWand'

noncomputable def cWandQ [CompleteLattice Pred]
    (H1 H2 : α → WithCredit Pred) : WithCredit Pred :=
  fun x => iInf fun a => cWand' (H1 a) (H2 a) x

namespace CreditT

theorem frame [Monad m] [Assertion Pred] [Assertion EPred] [WPMonad m Pred EPred]
    (H : Credit → Prop) (pre : WithCredit Pred) (post : α → WithCredit Pred)
    (epost : EPred) (x : CreditT m α) :
    Triple pre x post epost →
    Triple (⌜H⌝ᶜ ∗ᶜ pre) x (fun a => ⌜H⌝ᶜ ∗ᶜ post a) epost := by
  intro htriple
  rw [Triple.iff] at htriple ⊢
  intro crd
  unfold cStar cCredit
  apply iSup_le
  intro crdFrame
  rw [pure_intro_r]
  intro hframe_le
  rw [pure_intro_r]
  intro hframe
  apply PartialOrder.rel_trans
  · exact htriple (crd - crdFrame)
  apply le_iInf
  intro crdFrame'
  apply PartialOrder.rel_trans (iInf_le _ (crdFrame' + crdFrame))
  have hrun : crd - crdFrame + (crdFrame' + crdFrame) = crd + crdFrame' := by
    rw [Nat.add_comm crdFrame' crdFrame, ← Nat.add_assoc, Nat.sub_add_cancel hframe_le]
  rw [hrun]
  apply WPMonad.wp_consequence (m := m)
  intro ret
  apply le_meet
  · apply PartialOrder.rel_trans (meet_le_left _ _)
    exact LE.pure_imp _ _ (fun hret =>
      Nat.le_trans (Nat.le_add_right crdFrame' crdFrame) hret)
  · rw [pure_intro_r]
    intro hret
    apply PartialOrder.rel_trans _ (le_iSup (fun x1 =>
      ⌜x1 ≤ ret.2 - crdFrame'⌝ ⊓ (⌜H x1⌝ ⊓ post ret.1 (ret.2 - crdFrame' - x1))) crdFrame)
    apply le_meet
    · apply le_pure
      exact Nat.le_sub_of_add_le' hret
    · apply le_meet
      · exact le_pure _ _ hframe
      · have hpost :
            ret.2 - crdFrame' - crdFrame = ret.2 - (crdFrame' + crdFrame) := by
          rw [Nat.sub_sub]
        rw [hpost]

end CreditT


/-
∀ʰ f, (= f) -∗ wp x (fun x => (= f) ∗ post x) epost

fun h => ∀ f, (= f) -∗ wp x (fun x => (= f) ∗ post x) epost h
fun h => ∀ f, wp x (fun x => (= f) ∗ post x) epost (h + f)
fun h => ∀ f, wp (x.run (x + f)) (fun x h => (= f) ∗ post x) epost (h + f)

-/

end BasicRepr

namespace GhostReprTuple

open Singleton

abbrev Credit := Nat

structure CreditT (m : Type u → Type v) (α : Type u) where
  run : Ghost Credit → m (α × Ghost Credit)


/--
trace: [Compiler.result] size: 3
    def GhostReprTuple.CreditT.tick._redArg._lam_0._closed_0 : obj :=
      let _x.1 := ctor_0[Singleton.SingletonSet.mk'];
      let _x.2 := ctor_0[PUnit.unit];
      let _x.3 := ctor_0[Prod.mk] _x.2 _x.1;
      return _x.3
[Compiler.result] size: 3
    def GhostReprTuple.CreditT.tick._redArg._lam_0 toPure c : tobj :=
      let _x.1 := GhostReprTuple.CreditT.tick._redArg._lam_0._closed_0;
      inc[persistent][ref] _x.1;
      let _x.2 := toPure ◾ _x.1;
      return _x.2
[Compiler.result] size: 7
    def GhostReprTuple.CreditT.tick._redArg inst.1 : tobj :=
      let toApplicative := oproj[0] inst.1;
      inc[ref] toApplicative;
      dec[ref] inst.1;
      let toPure := oproj[1] toApplicative;
      inc toPure;
      dec[ref] toApplicative;
      let _f.2 := pap GhostReprTuple.CreditT.tick._redArg._lam_0 toPure;
      return _f.2
[Compiler.result] size: 1
    def GhostReprTuple.CreditT.tick m inst.1 : tobj :=
      let _x.2 := GhostReprTuple.CreditT.tick._redArg inst.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.result true in
def CreditT.tick [Monad m] : CreditT m Unit :=
  ⟨fun c => pure (f := m) ⟨(), c.modify (· + 1)⟩⟩

def Credit.default : Ghost Credit := SingletonSet.mk 0

protected def CreditT.pure [Monad m] (x : α) : CreditT m α where
  run := fun g => pure (x, g)

protected def CreditT.map [Monad m] (f : α → β) (x : CreditT m α) : CreditT m β where
  run := fun g => do
    let a ← x.run g
    pure (f a.fst, a.snd.modify (· + 1))

protected def CreditT.bind [Monad m] (x : CreditT m α) (f : α → CreditT m β) : CreditT m β :=
  ⟨fun c => do
    let ⟨a, c'⟩ ← x.run c
    (f a).run (c'.modify (· + 1))⟩

instance [Monad m] : Monad (CreditT m) where
  map := CreditT.map
  pure := CreditT.pure
  bind := CreditT.bind

def linearSearchArrayIdx? [Monad m] (p : α → Bool) (xs : Array α) : CreditT m (Option Nat) :=
  ⟨fun c =>
    let rec loop (i : Nat) (c : Ghost Credit) : Option Nat × Ghost Credit :=
      if h : i < xs.size then
        let (_, c) := (CreditT.tick (m := Id)).run c
        if p xs[i] then
          (some i, c)
        else
          loop (i + 1) c
      else
        (none, c)
    pure (loop 0 c)⟩

end GhostReprTuple

namespace GhostReprStructure

open Singleton

abbrev Credit := Nat

structure Result (α: Type u) where
    val: α
    credits: Ghost Credit

structure CreditT (m : Type u → Type v) (α : Type u) where
  run : Ghost Credit → m (Result α)

/--
trace: [Compiler.result] size: 3
    def GhostReprStructure.CreditT.tick._redArg._lam_0._closed_0 : obj :=
      let _x.1 := ctor_0[Singleton.SingletonSet.mk'];
      let _x.2 := ctor_0[PUnit.unit];
      let _x.3 := ctor_0[GhostReprStructure.Result.mk] _x.2 _x.1;
      return _x.3
[Compiler.result] size: 3
    def GhostReprStructure.CreditT.tick._redArg._lam_0 toPure c : tobj :=
      let _x.1 := GhostReprStructure.CreditT.tick._redArg._lam_0._closed_0;
      inc[persistent][ref] _x.1;
      let _x.2 := toPure ◾ _x.1;
      return _x.2
[Compiler.result] size: 7
    def GhostReprStructure.CreditT.tick._redArg inst.1 : tobj :=
      let toApplicative := oproj[0] inst.1;
      inc[ref] toApplicative;
      dec[ref] inst.1;
      let toPure := oproj[1] toApplicative;
      inc toPure;
      dec[ref] toApplicative;
      let _f.2 := pap GhostReprStructure.CreditT.tick._redArg._lam_0 toPure;
      return _f.2
[Compiler.result] size: 1
    def GhostReprStructure.CreditT.tick m inst.1 : tobj :=
      let _x.2 := GhostReprStructure.CreditT.tick._redArg inst.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.result true in
def CreditT.tick [Monad m] : CreditT m Unit :=
  ⟨fun c => pure (f := m) ⟨(), c.modify (· + 1)⟩⟩

def Credit.default : Ghost Credit := SingletonSet.mk 0


protected def CreditT.pure [Monad m] (x : α) : CreditT m α where
  run :=  fun g => do
      let res := ⟨x, g⟩
      pure res

-- While mapping, we want to run the function, and we also want to say that running the function took one tick?
protected def CreditT.map [Monad m] (f : α → β) (x : CreditT m α) : CreditT m β where
    run := fun g => do
        let a <- x.run g
        let b := f a.val
        pure ⟨b, a.credits.modify (· + 1)⟩


protected def CreditT.bind [Monad m] (x : CreditT m α) (f : α → CreditT m β) : CreditT m β :=
     ⟨fun c => do
       let ⟨a, c'⟩ ← x.run c
       (f a).run (c'.modify (· + 1))⟩


instance [Monad m] : Monad (CreditT m) where
  map := CreditT.map
  pure := CreditT.pure
  bind := CreditT.bind


def linearSearchArrayIdx? [Monad m] (p : α → Bool) (xs : Array α) : CreditT m (Option Nat) :=
  ⟨fun c =>
    let rec loop (i : Nat) (c : Ghost Credit) : Result (Option Nat) :=
      if h : i < xs.size then
        let ticked := (CreditT.tick (m := Id)).run c
        let c := ticked.credits
        if p xs[i] then
          ⟨some i, c⟩
        else
          loop (i + 1) c
      else
        ⟨none, c⟩
    pure (loop 0 c)⟩

end GhostReprStructure

namespace GhostReprStateT

open Singleton

abbrev Credit := Nat

abbrev CreditT (m : Type → Type v) (α : Type) :=
  StateT (Ghost Credit) m α

/--
trace: [Compiler.result] size: 9
    def GhostReprStateT.CreditT.tick._redArg inst.1 : tobj :=
      let toApplicative := oproj[0] inst.1;
      inc[ref] toApplicative;
      dec[ref] inst.1;
      let toPure := oproj[1] toApplicative;
      inc toPure;
      dec[ref] toApplicative;
      let _x.2 := GhostReprTuple.CreditT.tick._redArg._lam_0._closed_0;
      inc[persistent][ref] _x.2;
      let _x.3 := toPure ◾ _x.2;
      return _x.3
[Compiler.result] size: 1
    def GhostReprStateT.CreditT.tick m inst.1 c : tobj :=
      let _x.2 := GhostReprStateT.CreditT.tick._redArg inst.1;
      return _x.2
-/
#guard_msgs in
set_option trace.Compiler.result true in
def CreditT.tick [Monad m] : CreditT m Unit :=
  fun c => pure ((), c.modify (· + 1))

def Credit.default : Ghost Credit := SingletonSet.mk 0

def linearSearchArrayIdx? [Monad m] (p : α → Bool) (xs : Array α) : CreditT m (Option Nat) :=
  fun c =>
    let rec loop (i : Nat) (c : Ghost Credit) : Option Nat × Ghost Credit :=
      if h : i < xs.size then
        let (_, c) := (CreditT.tick (m := Id)).run c
        if p xs[i] then
          (some i, c)
        else
          loop (i + 1) c
      else
        (none, c)
    pure (loop 0 c)

end GhostReprStateT

namespace GhostReprStateRefT

open Singleton

abbrev Credit := Nat

abbrev CreditT (m : Type → Type) (α : Type) :=
  StateRefT' IO.RealWorld (Ghost Credit) m α

/--
trace: [Compiler.result] size: 5
    def GhostReprStateRefT.CreditT.tick._redArg inst.1 @&a : tobj :=
      let _f.2 := GhostReprTuple.CreditT.tick._at_.GhostReprTuple.linearSearchArrayIdx?.loop.spec_0._closed_0;
      inc[persistent][ref] _f.2;
      inc a;
      let _x.3 := pap ST.Prim.Ref.modifyGetUnsafe._boxed ◾ ◾ ◾ a _f.2;
      let _x.4 := inst.1 ◾ _x.3;
      return _x.4
[Compiler.result] size: 2
    def GhostReprStateRefT.CreditT.tick._redArg._boxed inst.1 a : tobj :=
      let res := GhostReprStateRefT.CreditT.tick._redArg inst.1 a;
      dec a;
      return res
[Compiler.result] size: 1
    def GhostReprStateRefT.CreditT.tick m inst.1 @&a : tobj :=
      let _x.2 := GhostReprStateRefT.CreditT.tick._redArg inst.1 a;
      return _x.2
[Compiler.result] size: 2
    def GhostReprStateRefT.CreditT.tick._boxed m inst.1 a : tobj :=
      let res := GhostReprStateRefT.CreditT.tick m inst.1 a;
      dec a;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
def CreditT.tick [MonadLiftT (ST IO.RealWorld) m] : CreditT m Unit :=
  StateRefT'.modifyGet fun c => ((), c.modify (· + 1))

def Credit.default : Ghost Credit := SingletonSet.mk 0

def linearSearchArrayIdx? [Monad m] [MonadLiftT (ST IO.RealWorld) m]
    (p : α → Bool) (xs : Array α) : CreditT m (Option Nat) :=
  let rec loop (i : Nat) : CreditT m (Option Nat) := do
    if h : i < xs.size then
      CreditT.tick
      if p xs[i] then
        return some i
      else
        loop (i + 1)
    else
      return none
  loop 0

end GhostReprStateRefT


/-
The Credit.tick implementation for the Ghost related implementation don't have
any of the ghost code (don't have increments caused via the tick). This is also
the case for the final generated C code. Performance is similar for all
ghost-variants -/
