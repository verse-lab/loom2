import Loom.Triple.Basic
import Loom.WP.SimpLemmas
import Plausible.Gen
import Plausible.Testable


open Lean.Order Loom

instance (priority := high) {σ : Type} {m : Type → Type v} [Monad m] [LawfulMonad m] [WP m Prop e] [Inhabited σ] :
  WP (StateT σ m) Prop e where
  wp x post epost := ∀ s, WP.wp (m := m) (x s) (post ·.1) epost
  wp_pure x post epost := by simp [pure, StateT.pure, WP.wp_pure (m := m)]
  wp_bind x f post epost := by
    intro wph s; apply WP.wp_bind (m := m)
    apply WP.wp_cons (m := m); rotate_left; apply wph
    intro x h; simp_all
  wp_cons x post post' epost h := by
    intro s s'; apply WP.wp_cons (m := m);
    intro x; apply h; solve_by_elim

instance (priority := high) [Monad m] [LawfulMonad m] [WP m Prop e] [Inhabited ρ] :
  WP (ReaderT ρ m) Prop e where
  wp x post epost := ∀ r, WP.wp (m := m) (x r) (post ·) epost
  wp_pure x post epost := by simp [pure, ReaderT.pure, WP.wp_pure (m := m)]
  wp_bind x f post epost := by
    intro wph r; apply WP.wp_bind (m := m)
    apply WP.wp_cons (m := m); rotate_left; apply wph
    intro x h; simp_all
  wp_cons x post post' epost h := by
    intro r r'; apply WP.wp_cons (m := m);
    intro x; apply h; solve_by_elim

instance (priority := high) : WP (Except ε) Prop PUnit where
  wp x post epost := match x with
    | .ok x => post x
    | .error e => False
  wp_pure x post epost := rfl
  wp_bind x f post epost := by cases x <;> exact id
  wp_cons x post post' epost h := by cases x with
    | ok a => exact h a
    | error e => exact id

open Plausible

theorem chooseAny_wp (post : α → Prop) [Random Id α] :
  Triple (∀ a, post a) (Gen.chooseAny α) post ⟨⟩ := by
  rw [Triple.iff]
  intro hpost
  simp [Gen.chooseAny, liftM, monadLift]
  intro s; simp; solve_by_elim

theorem Testable.run_wp [Testable p] c m :
  Triple (p ∧ post) (Testable.runPropE p c m) (fun _ => post) ⟨⟩ := by
  rw [Triple.iff]; intro ⟨ph, posth⟩
  simp [Testable.runPropE]; apply WP.wp_bind (m := Gen)
  simp [tryCatch, MonadExceptOf.tryCatch, tryCatchThe, Except.tryCatch]
  intro s r; simp
  split
  { simp [wp]; intro s r; split; solve_by_elim
    rename_i a _ _ _ _
    rcases a with ⟨⟨⟩, _⟩ <;> try simp_all [Functor.map, StateT.map, pure, StateT.pure, Except.pure, ReaderT.pure] }
  erw [WP.wp_pure]; simp; solve_by_elim
