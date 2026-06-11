

namespace MathlibErased

/-- `Erased α` is the same as `α`, except that the elements
  of `Erased α` are erased in the VM in the same way as types
  and proofs. This can be used to track data without storing it
  literally. -/
def Erased (α : Sort u) : Sort max 1 u :=
  { s : α → Prop // ∃ a, (a = ·) = s }

/-- Erase a value. -/
@[macro_inline, grind]
def hide {α} (a : α) : Erased α :=
  ⟨fun b => a = b, a, rfl⟩

/-- Extracts the erased value, noncomputably. -/
@[grind]
noncomputable def Erased.reveal {α} : Erased α → α
  | ⟨_, h⟩ => Classical.choose h 


@[ext, grind ., simp]
theorem reveal_inj {α} (a b : Erased α) (h : a.reveal  = b.reveal ) : a = b := by
        unfold Erased.reveal at *
        grind
/-
GhostStateT σ m

x : GST σ m α --> x.erase : m α 


WPMonad (GST σ m α) (σ → Pred) EPred

pre : Pred

post : α → σ → Pred

⦃ fun _ => pre ⦄ x ⦃ v, fun _ => post v ⦄

⦃ pre ⦄ x.erase ⦃ v, post v ⦄
-/

/-- `(>>=)` operation on `Erased`.

This is a separate definition because `α` and `β` can live in different
universes (the universe is fixed in `Monad`).
-/
@[grind]
def Erased.bind {α β} (a : Erased α) (f : α → Erased β) : Erased β :=
  ⟨fun b => (f a.reveal).1 b, (f a.reveal).2⟩

@[grind, simp]
def map {α β} (f : α → β) (a : Erased α) : Erased β :=
  a.bind (hide ∘ f)

instance instErasedM : Monad Erased where
  pure := @hide
  bind := @Erased.bind
  map := @map

@[simp]
theorem reveal_hide {α} (a : α) : (hide a : Erased α).reveal = a := by
  unfold Erased.reveal hide
  let h : ∃ x, (x = ·) = fun b => a = b := by
      simp
  change Classical.choose h = a
  have hs := Classical.choose_spec h
  have ht : (Classical.choose h = a) = (a = a) := congrFun hs a
  exact Eq.mpr ht rfl

@[simp]
theorem bind_eq {α β} (a : Erased α) (f : α → Erased β) : Erased.bind a f = f a.reveal := by
  unfold Erased.bind
  apply Subtype.ext
  rfl

instance instLawfulMonad : LawfulMonad Erased :=
  LawfulMonad.mk' Erased
    (id_map := by
      intro α x
      apply reveal_inj
      simp [Functor.map, map])
    (pure_bind := by
      intro α β x f
      simp [Bind.bind, Pure.pure])
    (bind_assoc := by
      intro α β γ x f g
      simp [Bind.bind])


def factorial (n: Nat) : Erased Nat :=
    if n <= 1 then hide 1
    else
        let rest := factorial ( n-1 )
        hide (n * rest.reveal)

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'Erased.reveal', which is 'noncomputable'
-/
#guard_msgs in
def factorial' (n: Nat) (acc: Nat) : Nat :=
    if n = 0 then acc
    else
        let res := factorial n
        res.reveal


namespace GhostStateCounter

abbrev GhostStateT (σ : Type u) (m : Type u → Type v) (α : Type u) := StateT (Erased σ ) m α

abbrev Counter := Nat

def sumFirstN_Ghost (n: Nat) : GhostStateT Counter Id Nat := do
    let mut sm := 0
    for i in [1:n] do
        let cnt <- get
        set ( (· + 1) <$> cnt )
        sm := sm + i
    pure sm

/- set_option trace.compiler.ir.result true in -/
def sumFirstN_NoGhost (n: Nat) : Id Nat := do
    let mut sm := 0
    for i in [1:n] do
        sm := sm + i
    pure sm

theorem sumFirstN_loop_equiv (xs : List Nat) (sm : Nat) (cntr : Erased Counter) :
    List.foldl (fun b a => b + a) sm xs =
      (((forIn xs sm fun i r => do
          let cnt ← get
          set ((fun x => x + 1) <$> cnt)
          pure (ForInStep.yield (r + i))) : GhostStateT Counter Id Nat).run cntr).fst := by
  induction xs generalizing sm cntr with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl, List.forIn_cons]
      exact ih (sm + x) (((fun x => x + 1) <$> cntr))

theorem equiv : ∀ n cntr, sumFirstN_NoGhost n  =  ((sumFirstN_Ghost n).run cntr).fst := by
        intros n cntr
        change Id.run (sumFirstN_NoGhost n) = ((sumFirstN_Ghost n).run cntr).fst
        simp [sumFirstN_NoGhost, sumFirstN_Ghost]
        exact sumFirstN_loop_equiv (List.range' 1 (n - 1)) 0 cntr

end GhostStateCounter

end MathlibErased


namespace Singleton
open Lean.Order

def Set (α : Type u) : Type u := α → Prop

def Set.mem (x : α) (s : Set α) : Prop := s x

def Set.mkSingleton (x : α) : Set α := fun y => y = x

inductive Set.IsSingleton (s : Set α) : Prop where
  | intro (x : α) : (∀ y, s.mem y ↔ y = x) → s.IsSingleton

theorem Set.mk_singleton_is_singleton (x : α) : (Set.mkSingleton x).IsSingleton := by
  apply Set.IsSingleton.intro x
  simp [mkSingleton, mem]

structure SingletonSet (α : Type u) where
  mk' ::
  toSet : Set α
  isSingleton : toSet.IsSingleton

def SingletonSet.mk (x : α) : SingletonSet α := ⟨Set.mkSingleton x, Set.mk_singleton_is_singleton x⟩

def SingletonSet.exists_unique (s : SingletonSet α) : ∃ x, ∀ y, s.toSet.mem y ↔ y = x := by
  rcases s.isSingleton with ⟨x, hx⟩
  exact ⟨x, hx⟩

noncomputable
def SingletonSet.get (s : SingletonSet α) : α := s.exists_unique.choose

theorem SingletonSet.mk_get_eq_self (x : α) : (SingletonSet.mk x).get = x := by
  have h := Classical.choose_spec (SingletonSet.mk x).exists_unique
  exact ((h x).mp (by simp [SingletonSet.mk, Set.mkSingleton, Set.mem])).symm

theorem SingletonSet.mk_get (s : SingletonSet α) : SingletonSet.mk s.get = s := by
  cases s with
  | mk' toSet isSingleton =>
    unfold SingletonSet.mk
    congr
    funext y
    apply propext
    have h := Classical.choose_spec (SingletonSet.mk' toSet isSingleton).exists_unique
    constructor
    · intro hy
      exact (h y).mpr hy
    · intro hy
      exact (h y).mp hy

-- This is computable unlike `get`!
def SingletonSet.modify (s : SingletonSet α) (f : α → α) : SingletonSet α :=
  ⟨fun x => ∃ y, s.toSet.mem y ∧ f y = x,
  by
    rcases s.isSingleton with ⟨x, hx⟩
    apply Set.IsSingleton.intro (f x)
    intro y
    constructor
    · rintro ⟨z, hz, hfz⟩
      calc
        y = f z := hfz.symm
        _ = f x := congrArg f ((hx z).mp hz)
    · intro hy
      exact ⟨x, (hx x).mpr rfl, hy.symm⟩ ⟩

theorem SingletonSet.modify_get (s : SingletonSet α) (f : α → α) : (s.modify f).get = f (s.get) := by
  have hs := Classical.choose_spec s.exists_unique
  have hmod := Classical.choose_spec (s.modify f).exists_unique
  have hsget : s.toSet.mem s.get := (hs s.get).mpr rfl
  exact ((hmod (f s.get)).mp ⟨s.get, hsget, rfl⟩).symm


abbrev Ghost (α : Type u) : Type u := SingletonSet α

end Singleton


namespace ReprExperiments

/--
trace: [Compiler.result] size: 1
    def ReprExperiments.foo @&n : tobj :=
      inc n;
      return n
[Compiler.result] size: 2
    def ReprExperiments.foo._boxed n : tobj :=
      let res := ReprExperiments.foo n;
      dec n;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
/- set_option trace.compiler.ir.result true in -/
def foo (n: {n': Nat // n' > 10 }) : Nat :=
    n.val


/--
trace: [Compiler.result] size: 1
    def ReprExperiments.foo_id @&n : tobj :=
      inc n;
      return n
[Compiler.result] size: 2
    def ReprExperiments.foo_id._boxed n : tobj :=
      let res := ReprExperiments.foo_id n;
      dec n;
      return res
-/
#guard_msgs in
set_option trace.Compiler.result true in
def foo_id (n: Nat) : Nat :=
    n


/--
trace: [Compiler.result] size: 1
    def ReprExperiments.foo'._redArg @&n : tobj :=
      inc n;
      return n
[Compiler.result] size: 2
    def ReprExperiments.foo'._redArg._boxed n : tobj :=
      let res := ReprExperiments.foo'._redArg n;
      dec n;
      return res
[Compiler.result] size: 1
    def ReprExperiments.foo' @&n h : tobj :=
      inc n;
      return n
[Compiler.result] size: 2
    def ReprExperiments.foo'._boxed n h : tobj :=
      let res := ReprExperiments.foo' n h;
      dec n;
      return res
---
warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
set_option trace.Compiler.result true in
def foo' (n: Nat) (h: n > 10) : Nat :=
    n


/--
trace: [Compiler.result] size: 1
    def ReprExperiments.foo'_tup._redArg n : obj :=
      let _x.1 := ctor_0[Prod.mk] n ◾;
      return _x.1
[Compiler.result] size: 1
    def ReprExperiments.foo'_tup n h : obj :=
      let _x.1 := ctor_0[Prod.mk] n ◾;
      return _x.1
---
warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
set_option trace.Compiler.result true in
def foo'_tup (n: Nat) (h: n > 10) : ( Nat × Prop) :=
    (n, True)



/--
trace: [Compiler.result] size: 1
    def ReprExperiments.foo'_struct._redArg @&n : tobj :=
      inc n;
      return n
[Compiler.result] size: 2
    def ReprExperiments.foo'_struct._redArg._boxed n : tobj :=
      let res := ReprExperiments.foo'_struct._redArg n;
      dec n;
      return res
[Compiler.result] size: 1
    def ReprExperiments.foo'_struct @&n h : tobj :=
      inc n;
      return n
[Compiler.result] size: 2
    def ReprExperiments.foo'_struct._boxed n h : tobj :=
      let res := ReprExperiments.foo'_struct n h;
      dec n;
      return res
---
warning: unused variable `h`

Note: This linter can be disabled with `set_option linter.unusedVariables false`
-/
#guard_msgs in
set_option trace.Compiler.result true in
def foo'_struct (n: Nat) (h: n > 10) : { s : Nat // s = n } :=
    ⟨n, by rfl⟩ 

end ReprExperiments

