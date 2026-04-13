import Loom.Triple.Basic
import Loom.WP.SimpLemmas
import Plausible.Gen
import Plausible.Testable


open Lean.Order Loom

instance (priority := high) {σ : Type} {m : Type → Type v} [Monad m] [LawfulMonad m] [WPMonad m Prop e] [Inhabited σ] :
  WPMonad (StateT σ m) Prop e where
  wpImpl x post epost := ∀ s, wp (m := m) (x s) (fun p => post p.1) epost
  wp_pure_impl x post epost := by
    intro hx s
    exact (WPMonad.wp_pure (m := m) (x := (x, s)) (post := fun p => post p.1) (epost := epost)) hx
  wp_bind_impl x f post epost := by
    intro wph s; apply WPMonad.wp_bind (m := m)
    apply WPMonad.wp_cons (m := m); rotate_left; apply wph
    intro x h; simp_all
  wp_cons_impl x post post' epost h := by
    intro s s'; apply WPMonad.wp_cons (m := m);
    intro x; apply h; solve_by_elim

instance (priority := high) [Monad m] [LawfulMonad m] [WPMonad m Prop e] [Inhabited ρ] :
  WPMonad (ReaderT ρ m) Prop e where
  wpImpl x post epost := ∀ r, wp (m := m) (x r) post epost
  wp_pure_impl x post epost := by
    intro hx r
    exact (WPMonad.wp_pure (m := m) (x := x) (post := post) (epost := epost)) hx
  wp_bind_impl x f post epost := by
    intro wph r; apply WPMonad.wp_bind (m := m)
    apply WPMonad.wp_cons (m := m); rotate_left; apply wph
    intro x h; simp_all
  wp_cons_impl x post post' epost h := by
    intro r r'; apply WPMonad.wp_cons (m := m);
    intro x; apply h; solve_by_elim

instance (priority := high) : WPMonad (Except ε) Prop PUnit where
  wpImpl x post epost := match x with
    | .ok x => post x
    | .error e => False
  wp_pure_impl x post epost := PartialOrder.rel_refl
  wp_bind_impl x f post epost := by cases x <;> exact id
  wp_cons_impl x post post' epost h := by cases x with
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
  simp [Testable.runPropE]; apply WPMonad.wp_bind (m := Gen)
  simp [tryCatch, MonadExceptOf.tryCatch, tryCatchThe, Except.tryCatch]
  intro s r; simp
  split
  { simp only [wp, WPMonad.wpImpl]
    intro s r; split; solve_by_elim
    rename_i a _ _ _ _
    rcases a with ⟨⟨⟩, _⟩ <;> try simp_all [Functor.map, StateT.map, pure, StateT.pure, Except.pure, ReaderT.pure] }
  have hgave : wp (pure (TestResult.gaveUp 1) : Gen (TestResult p)) (fun _ => post) PUnit.unit :=
    (WPMonad.wp_pure (m := Gen) (x := TestResult.gaveUp 1)
      (post := fun _ => post) (epost := PUnit.unit)) posth
  simpa [pure, StateT.pure, ReaderT.pure] using hgave
