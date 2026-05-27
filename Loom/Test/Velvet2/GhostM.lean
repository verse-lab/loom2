-- From mathlib:     Mathlib/Data/Erased.lean

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

abbrev GhostM := Erased

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
