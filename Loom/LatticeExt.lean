import Init.Internal.Order

universe u v w

open Lean.Order

-- namespace VelvetSimple

/-!
# Additional Complete Lattice Operations

Extensions to Lean.Order.CompleteLattice providing additional operations
needed for program verification.
-/

section LatticeExtensions

attribute [refl] PartialOrder.rel_refl

instance : PartialOrder Unit where
  rel _ _ := True
  rel_refl := trivial
  rel_trans _ _ := trivial
  rel_antisymm _ _ := rfl

instance : CompleteLattice Unit where
  has_sup _ := ⟨(), fun _ => ⟨fun _ _ _ => trivial, fun _ => trivial⟩⟩

instance : PartialOrder PUnit where
  rel _ _ := True
  rel_refl := trivial
  rel_trans _ _ := trivial
  rel_antisymm _ _ := rfl

instance : CompleteLattice PUnit where
  has_sup _ := ⟨.unit, fun _ => ⟨fun _ _ _ => trivial, fun _ => trivial⟩⟩

instance [PartialOrder α] [PartialOrder β] : PartialOrder (α × β) where
  rel a b := a.1 ⊑ b.1 ∧ a.2 ⊑ b.2
  rel_refl := ⟨PartialOrder.rel_refl, PartialOrder.rel_refl⟩
  rel_trans ha hb := ⟨PartialOrder.rel_trans ha.1 hb.1, PartialOrder.rel_trans ha.2 hb.2⟩
  rel_antisymm ha hb := Prod.ext (PartialOrder.rel_antisymm ha.1 hb.1) (PartialOrder.rel_antisymm ha.2 hb.2)

instance [CompleteLattice α] [CompleteLattice β] : CompleteLattice (α × β) where
  has_sup c :=
    ⟨(CompleteLattice.sup (fun a => ∃ b, c (a, b)),
      CompleteLattice.sup (fun b => ∃ a, c (a, b))), fun x => ⟨
      fun ⟨h1, h2⟩ y hy => ⟨PartialOrder.rel_trans (le_sup _ ⟨y.2, hy⟩) h1,
                              PartialOrder.rel_trans (le_sup _ ⟨y.1, hy⟩) h2⟩,
      fun h => ⟨sup_le _ fun a ⟨b, hab⟩ => (h (a, b) hab).1,
               sup_le _ fun b ⟨a, hab⟩ => (h (a, b) hab).2⟩⟩⟩

variable {α : Type u} [CompleteLattice α]

/-- Top element of a complete lattice (supremum of all elements) -/
noncomputable def latticeTop : α := CompleteLattice.sup (fun _ => True)

notation "⊤" => latticeTop

theorem le_top (x : α) : x ⊑ ⊤ := by
  apply le_sup
  trivial

/-- Bottom element of a complete lattice (infimum of all elements) -/
noncomputable def latticeBot : α := inf (fun _ => True)

theorem latticeBot_le (x : α) : latticeBot ⊑ x := by
  apply inf_le
  trivial

/-- Binary meet (infimum) -/
noncomputable def meet (x y : α) : α := inf (fun z => z = x ∨ z = y)

infixl:70 " ⊓ " => meet

theorem meet_le_left (x y : α) : x ⊓ y ⊑ x := by
  apply inf_le
  left; rfl

theorem meet_le_right (x y : α) : x ⊓ y ⊑ y := by
  apply inf_le
  right; rfl

theorem le_meet (x y z : α) : x ⊑ y → x ⊑ z → x ⊑ y ⊓ z := by
  intro hxy hxz
  apply le_inf
  intro w hw
  cases hw with
  | inl h => rw [h]; exact hxy
  | inr h => rw [h]; exact hxz

/-- Binary join (supremum) -/
noncomputable def join (x y : α) : α := CompleteLattice.sup (fun z => z = x ∨ z = y)

infixl:65 " ⊔ " => join

theorem left_le_join (x y : α) : x ⊑ x ⊔ y := by
  apply le_sup
  left; rfl

theorem right_le_join (x y : α) : y ⊑ x ⊔ y := by
  apply le_sup
  right; rfl

theorem join_le (x y z : α) : x ⊑ z → y ⊑ z → x ⊔ y ⊑ z := by
  intro hxz hyz
  apply sup_le
  intro w hw
  cases hw with
  | inl h => rw [h]; exact hxz
  | inr h => rw [h]; exact hyz

/-- Indexed infimum -/
noncomputable def iInf {ι : Type v} (f : ι → α) : α := inf (fun x => ∃ i, f i = x)

theorem iInf_le {ι : Type v} (f : ι → α) (i : ι) : iInf f ⊑ f i := by
  apply inf_le
  exact ⟨i, rfl⟩

theorem le_iInf {ι : Type v} (f : ι → α) (x : α) : (∀ i, x ⊑ f i) → x ⊑ iInf f := by
  intro h
  apply le_inf
  intro y ⟨i, hi⟩
  rw [← hi]
  exact h i

/-- Indexed supremum -/
noncomputable def iSup {ι : Type v} (f : ι → α) : α := CompleteLattice.sup (fun x => ∃ i, f i = x)

theorem le_iSup {ι : Type v} (f : ι → α) (i : ι) : f i ⊑ iSup f := by
  apply le_sup
  exact ⟨i, rfl⟩

theorem iSup_le {ι : Type v} (f : ι → α) (x : α) : (∀ i, f i ⊑ x) → iSup f ⊑ x := by
  intro h
  apply sup_le
  intro y ⟨i, hi⟩
  rw [← hi]
  exact h i

-- /-- For function types, the top element evaluates pointwise to top -/
-- theorem latticeTop_fun_apply {σ : Type u} {α : Type u} [CompleteLattice α] (s : σ) :
--     (⊤ : σ → α) s = (⊤ : α) := by
--   apply PartialOrder.rel_antisymm
--   · exact le_top _
--   · apply le_sup
--     exact ⟨fun _ => ⊤, trivial, rfl⟩

-- /-- For function types, the bot element evaluates pointwise to bot -/
-- theorem latticeBot_fun_apply {σ : Type u} {α : Type u} [CompleteLattice α] (s : σ) :
--     (latticeBot : σ → α) s = (latticeBot : α) := by
--   apply PartialOrder.rel_antisymm
--   · apply inf_le
--     exact ⟨fun _ => latticeBot, trivial, rfl⟩
--   · exact latticeBot_le _

end LatticeExtensions

/-!
# LawfulMonadLiftT instances

Effect observation instances for common monad transformers.
-/

instance instLawfulMonadLiftTRefl [Monad m] : LawfulMonadLiftT m m where
  monadLift_pure := by simp
  monadLift_bind := by simp

instance instLawfulMonadLiftTStateT [Monad m] [LawfulMonad m] : LawfulMonadLiftT m (StateT σ m) where
  monadLift_pure := by simp
  monadLift_bind := by simp

instance instLawfulMonadLiftTReaderT [Monad m] [LawfulMonad m] : LawfulMonadLiftT m (ReaderT σ m) where
  monadLift_pure := by simp
  monadLift_bind := by simp

instance instLawfulMonadLiftTExceptT [Monad m] [LawfulMonad m] : LawfulMonadLiftT m (ExceptT ε m) where
  monadLift_pure := by simp
  monadLift_bind := by simp

instance instLawfulMonadLiftTTrans [Monad m] [LawfulMonad m]
  [Monad n] [LawfulMonad n] [MonadLiftT m n] [LawfulMonadLiftT m n]
  [Monad p] [LawfulMonad p] [MonadLift n p] [LawfulMonadLiftT n p]
  : LawfulMonadLiftT m p where
    monadLift_pure := by simp
    monadLift_bind := by simp

/-!
# Prop Embedding into Partial Order

Embedding propositions into a partial order with top and bottom.
-/

open Classical in
noncomputable def LE.pure {l : Type u} [CompleteLattice l] : Prop → l := fun p =>
  if p then ⊤ else latticeBot

macro "⌜" p:term "⌝" : term => `(LE.pure $p)

@[app_unexpander LE.pure] def unexpandPure : Lean.PrettyPrinter.Unexpander
  | `($(_) $p) => `(⌜$p⌝)
  | _ => throw ()

@[simp]
theorem trueE (l : Type v) [CompleteLattice l] : ⌜True⌝ = (⊤ : l) := by
  simp [LE.pure]

@[simp]
theorem falseE (l : Type v) [CompleteLattice l] : ⌜False⌝ = (latticeBot : l) := by
  simp [LE.pure]

open Classical in
theorem LE.pure_imp {l : Type u} [CompleteLattice l]
  (p₁ p₂ : Prop) : (p₁ → p₂) → ⌜p₁⌝ ⊑ (⌜p₂⌝ : l) := by
  simp only [LE.pure]
  intro h
  split
  case isTrue hp1 =>
    split
    case isTrue => exact PartialOrder.rel_refl
    case isFalse hp2 => exact absurd (h hp1) hp2
  case isFalse =>
    exact latticeBot_le _

@[simp]
theorem LE.pure_intro {l : Type u} [CompleteLattice l]
  (p : Prop) (h : l) : (⌜p⌝ ⊑ h) = (p → ⊤ ⊑ h) := by
  simp only [LE.pure]
  apply propext
  constructor
  · intro hle hp
    simp only [hp, ↓reduceIte] at hle
    exact hle
  · intro himp
    split
    next hp => exact himp hp
    next => exact latticeBot_le _

@[simp]
theorem pure_intro_l {l : Type u} [CompleteLattice l] (p : Prop) (x y : l) :
  (x ⊓ ⌜ p ⌝ ⊑ y) = (p → x ⊑ y) := by
  apply propext
  constructor
  · intro h hp
    have hxy : x ⊓ ⊤ ⊑ y := by simp only [LE.pure, hp, ↓reduceIte] at h; exact h
    have hx_le_meet : x ⊑ x ⊓ ⊤ := le_meet x x ⊤ PartialOrder.rel_refl (le_top x)
    exact PartialOrder.rel_trans hx_le_meet hxy
  · intro h
    simp only [LE.pure]
    split
    next hp => exact PartialOrder.rel_trans (meet_le_left x ⊤) (h hp)
    next => exact PartialOrder.rel_trans (meet_le_right x latticeBot) (latticeBot_le _)

@[simp]
theorem pure_intro_r {l : Type u} [CompleteLattice l] (p : Prop) (x y : l) :
  (⌜ p ⌝ ⊓ x ⊑ y) = (p → x ⊑ y) := by
  apply propext
  constructor
  · intro h hp
    have hxy : ⊤ ⊓ x ⊑ y := by simp only [LE.pure, hp, ↓reduceIte] at h; exact h
    have hx_le_meet : x ⊑ ⊤ ⊓ x := le_meet x ⊤ x (le_top x) PartialOrder.rel_refl
    exact PartialOrder.rel_trans hx_le_meet hxy
  · intro h
    simp only [LE.pure]
    split
    next hp => exact PartialOrder.rel_trans (meet_le_right ⊤ x) (h hp)
    next => exact PartialOrder.rel_trans (meet_le_left latticeBot x) (latticeBot_le _)

/-!
# CompleteLattice instance for Prop

We define a CompleteLattice structure on Prop where:
- rel is implication (→)
- sup is existential quantification over the predicate
-/

instance : PartialOrder Prop where
  rel p q := p → q
  rel_refl := id
  rel_trans := fun h1 h2 x => h2 (h1 x)
  rel_antisymm := fun h1 h2 => propext ⟨h1, h2⟩

/-- Supremum for Prop: true iff some element of the set is true -/
def propSup (c : Prop → Prop) : Prop := ∃ p, c p ∧ p

theorem propSup_is_sup (c : Prop → Prop) : is_sup c (propSup c) := by
  intro y
  constructor
  · -- mp: (propSup c → y) → (∀ z, c z → z → y)
    intro hsup z hcz hz
    apply hsup
    exact Exists.intro z (And.intro hcz hz)
  · -- mpr: (∀ z, c z → z → y) → (propSup c → y)
    intro h ⟨z, hcz, hz⟩
    exact h z hcz hz

instance : CompleteLattice Prop where
  has_sup c := ⟨propSup c, propSup_is_sup c⟩
