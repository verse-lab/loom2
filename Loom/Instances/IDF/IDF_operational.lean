import Loom.Instances.IDF.IDF_extended

open Classical

set_option autoImplicit false

namespace IDFOperational

variable {α β γ : Type}

inductive ChoiceTree (α : Type) where
  | ret : α → ChoiceTree α
  | demonic : {ι : Type} → (ι → ChoiceTree α) → ChoiceTree α
  | angelic : {ι : Type} → (ι → ChoiceTree α) → ChoiceTree α

namespace ChoiceTree

def bind (x : ChoiceTree α) (f : α → ChoiceTree β) : ChoiceTree β :=
  match x with
  | ret a => f a
  | demonic k => demonic (fun i => bind (k i) f)
  | angelic k => angelic (fun i => bind (k i) f)

instance : Monad ChoiceTree where
  pure := ret
  bind := bind

def wp (x : ChoiceTree α) (post : α → Prop) : Prop :=
  match x with
  | ret a => post a
  | demonic k => ∀ i, wp (k i) post
  | angelic k => ∃ i, wp (k i) post

def fail : ChoiceTree α :=
  angelic (ι := Empty) (fun e => nomatch e)

@[simp] theorem wp_ret (a : α) (post : α → Prop) :
    wp (ret a) post ↔ post a := by
  rfl

@[simp] theorem wp_demonic {ι : Type} (k : ι → ChoiceTree α) (post : α → Prop) :
    wp (demonic k) post ↔ ∀ i, wp (k i) post := by
  rfl

@[simp] theorem wp_angelic {ι : Type} (k : ι → ChoiceTree α) (post : α → Prop) :
    wp (angelic k) post ↔ ∃ i, wp (k i) post := by
  rfl

@[simp] theorem wp_fail (post : α → Prop) :
    wp (fail : ChoiceTree α) post ↔ False := by
  constructor
  · intro h
    rcases h with ⟨i, _⟩
    cases i
  · intro h
    exact False.elim h

@[simp] theorem bind_ret (x : ChoiceTree α) :
    bind x ret = x := by
  induction x with
  | ret a => rfl
  | demonic k ih =>
      simp [bind, ih]
  | angelic k ih =>
      simp [bind, ih]

@[simp] theorem ret_bind (a : α) (f : α → ChoiceTree β) :
    bind (ret a) f = f a := by
  rfl

@[simp] theorem bind_assoc (x : ChoiceTree α) (f : α → ChoiceTree β) (g : β → ChoiceTree γ) :
    bind (bind x f) g = bind x (fun a => bind (f a) g) := by
  induction x with
  | ret a => rfl
  | demonic k ih =>
      simp [bind, ih]
  | angelic k ih =>
      simp [bind, ih]

@[simp] theorem wp_bind (x : ChoiceTree α) (f : α → ChoiceTree β) (post : β → Prop) :
    wp (bind x f) post ↔ wp x (fun a => wp (f a) post) := by
  induction x with
  | ret a =>
      rfl
  | demonic k ih =>
      simp [bind, wp, ih]
  | angelic k ih =>
      simp [bind, wp, ih]

theorem wp_monotone (x : ChoiceTree α) {post post' : α → Prop}
    (hpost : ∀ a, post a → post' a) :
    wp x post → wp x post' := by
  induction x with
  | ret a =>
      exact hpost a
  | demonic k ih =>
      intro hx i
      exact ih i (hx i)
  | angelic k ih =>
      rintro ⟨i, hi⟩
      exact ⟨i, ih i hi⟩

instance : LawfulMonad ChoiceTree := by
  refine LawfulMonad.mk' ChoiceTree ?_ ?_ ?_
  · intro α x
    change bind x ret = x
    exact bind_ret x
  · intros
    rfl
  · intros
    exact bind_assoc _ _ _

instance : Loom.WPMonad ChoiceTree Prop EPost⟨⟩ where
  wpTrans x := fun post _ => wp x post
  wp_trans_pure x := by
    intro post _ h
    exact h
  wp_trans_bind x f := by
    intro post _ h
    exact (wp_bind x f post).2 h
  wp_trans_monotone x := by
    intro post post' _ _ _ hpost
    exact ChoiceTree.wp_monotone x hpost

end ChoiceTree

abbrev ViperM (α : Type) := StateT VirtualState ChoiceTree α

namespace ViperM

def fail : ViperM α :=
  fun _ => ChoiceTree.fail

def InhaleChoice (ω : VirtualState) (hp : Assertion) : Type :=
  { p : VirtualState × VirtualState //
      hp p.1 ∧ VirtualState.plus ω p.1 = some p.2 ∧ p.2.Stable }

def ExhaleChoice (ω : VirtualState) (hp : Assertion) : Type :=
  { p : VirtualState × VirtualState //
      hp p.2 ∧ VirtualState.plus p.1 p.2 = some ω ∧ p.1.Stable }

noncomputable def inhale (hp : Assertion) : ViperM PUnit :=
  fun ω =>
    if Assertion.rel_stable_assertion ω hp then
      .demonic (ι := InhaleChoice ω hp) (fun p => .ret (PUnit.unit, p.1.2))
    else
      ChoiceTree.fail

noncomputable def exhale (hp : Assertion) : ViperM PUnit :=
  fun ω =>
    .angelic (ι := ExhaleChoice ω hp) (fun p => .ret (PUnit.unit, p.1.1))

theorem wp_inhale_eq_wp_inhale_op (hp : Assertion) (post : Unit → Assertion) :
    Loom.wp (inhale hp) post epost⟨⟩ = Assertion.wp_inhale_op hp post := by
  funext ω
  apply propext
  rw [Loom.StateT.apply_wp]
  change ChoiceTree.wp (inhale hp ω) (fun p => post p.1 p.2) ↔ Assertion.wp_inhale_op hp post ω
  by_cases hframes : Assertion.rel_stable_assertion ω hp
  · constructor
    · intro h
      refine ⟨hframes, ?_⟩
      simp [inhale, hframes, ChoiceTree.wp] at h
      intro ω_hp ω' hhp hplus hstable
      exact h ⟨(ω_hp, ω'), hhp, hplus, hstable⟩
    · rintro ⟨_, h⟩
      simp [inhale, hframes, ChoiceTree.wp]
      intro p
      exact h p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2
  · constructor
    · intro h
      simp [inhale, hframes, ChoiceTree.fail] at h
      rcases h with ⟨i, _⟩
      cases i
    · intro h
      exact False.elim (hframes h.1)

theorem wp_exhale_eq_wp_exhale_op (hp : Assertion) (post : Unit → Assertion) :
    Loom.wp (exhale hp) post epost⟨⟩ = Assertion.wp_exhale_op hp post := by
  funext ω
  apply propext
  rw [Loom.StateT.apply_wp]
  change ChoiceTree.wp (exhale hp ω) (fun p => post p.1 p.2) ↔ Assertion.wp_exhale_op hp post ω
  constructor
  · intro h
    simp [exhale, ChoiceTree.wp] at h
    rcases h with ⟨p, hpst⟩
    exact ⟨p.1.1, p.1.2, p.2.1, p.2.2.1, p.2.2.2, hpst⟩
  · intro h
    simp [exhale, ChoiceTree.wp]
    rcases h with ⟨ω', ωA, hA, hplus, hstable, hpost⟩
    exact ⟨⟨(ω', ωA), hA, hplus, hstable⟩, hpost⟩

end ViperM

end IDFOperational
