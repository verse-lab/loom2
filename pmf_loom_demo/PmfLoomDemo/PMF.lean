import Loom.Triple.Basic
-- import Loom.Tactic.VCGen
import Mathlib.Probability.ProbabilityMassFunction.Constructions

open Lean.Order Std.Do'
open scoped ENNReal

namespace PMF

/-!
This module connects mathlib's concrete `PMF` monad to Loom's custom WP class.

Mathlib's `PMF α` stores a probability mass function `α → ENNReal` with total mass `1`.
For Loom, we expose it through weakest pre-expectations: a distribution maps a
post-expectation `α → ENNReal` to its expected value.

The bridge is intentionally small. Loom currently uses `Lean.Order.CompleteLattice`,
which is separate from mathlib's order hierarchy, so this demo provides the
corresponding Loom lattice structure on `ENNReal` from mathlib's complete lattice.
-/

noncomputable instance instLeanOrderCompleteLatticeENNReal :
    Lean.Order.CompleteLattice ENNReal where
  rel x y := x ≤ y
  rel_refl := le_rfl
  rel_trans := fun hxy hyz => le_trans hxy hyz
  rel_antisymm := fun hxy hyx => le_antisymm hxy hyx
  has_sup c := by
    refine ⟨sSup {x : ENNReal | c x}, ?_⟩
    intro x
    constructor
    · intro hs y hy
      exact le_trans (le_sSup hy) hs
    · intro h
      exact sSup_le h

attribute [local instance] instLeanOrderCompleteLatticeENNReal

/-- Expected value of an `ENNReal` post-expectation under a mathlib `PMF`. -/
noncomputable def expect (p : PMF α) (post : α → ENNReal) : ENNReal :=
  ∑' a, p a * post a

theorem expect_pure (a : α) (post : α → ENNReal) :
    expect (pure a : PMF α) post = post a := by
  simp [expect, PMF.pure_apply]

theorem expect_bind (p : PMF α) (f : α → PMF β) (post : β → ENNReal) :
    expect (p >>= f) post = expect p (fun a => expect (f a) post) := by
  simp only [expect]
  calc
    (∑' b, (∑' a, p a * f a b) * post b)
        = ∑' b, ∑' a, p a * (f a b * post b) := by
          apply tsum_congr
          intro b
          rw [← ENNReal.tsum_mul_right]
          simp only [mul_assoc]
    _ = ∑' a, ∑' b, p a * (f a b * post b) := ENNReal.tsum_comm
    _ = ∑' a, p a * ∑' b, f a b * post b := by
          apply tsum_congr
          intro a
          rw [ENNReal.tsum_mul_left]

theorem expect_map (p : PMF α) (f : α → β) (post : β → ENNReal) :
    expect (f <$> p) post = expect p (fun a => post (f a)) := by
  rw [PMF.monad_map_eq_map, ← PMF.bind_pure_comp]
  change expect (p >>= (pure ∘ f)) post = expect p (fun a => post (f a))
  rw [expect_bind]
  apply congrArg
  funext a
  simp [expect_pure]

theorem expect_const_one (p : PMF α) :
    expect p (fun _ => (1 : ENNReal)) = 1 := by
  unfold expect
  simp [p.tsum_coe]

theorem expect_mono (p : PMF α) {post post' : α → ENNReal} :
    post ⊑ post' → expect p post ⊑ expect p post' := by
  intro hpost
  exact ENNReal.tsum_le_tsum fun a => mul_le_mul_right (hpost a) (p a)

noncomputable instance instWPLoomPMF : WP PMF ENNReal EPost.nil where
  wpTrans p := ⟨fun post _epost => expect p post⟩
  wp_trans_pure a := by
    intro post _epost
    change post a ⊑ expect (pure a : PMF _) post
    rw [expect_pure]
  wp_trans_bind p f := by
    intro post _epost
    change expect p (fun a => expect (f a) post) ⊑ expect (p >>= f) post
    rw [expect_bind]
  wp_trans_monotone p := by
    intro post post' _epost _epost' _hepost hpost
    exact expect_mono p hpost

@[simp]
theorem wp_apply (p : PMF α) (post : α → ENNReal) (epost : EPost.nil) :
    wp p post epost = expect p post :=
  rfl

/--
Read a natural-number counter and, with probability `p`, increment it by one.
This is a one-step random walk toward a threshold.
-/
noncomputable def maybeIncrement
    (p : NNReal) (hp : p ≤ 1) : StateT Nat PMF PUnit := do
  let tick ← PMF.bernoulli p hp
  modify (· + if tick then 1 else 0)

noncomputable def maybeIncrementRun
    (p : NNReal) (hp : p ≤ 1) (n : Nat) : PMF (PUnit × Nat) :=
  (fun tick => (⟨⟩, n + if tick then 1 else 0)) <$> PMF.bernoulli p hp

theorem maybeIncrement_run (p : NNReal) (hp : p ≤ 1) (n : Nat) :
    (maybeIncrement p hp).run n = maybeIncrementRun p hp n := by
  unfold maybeIncrement maybeIncrementRun
  ext r
  simp [StateT.run_bind, StateT.run_monadLift, StateT.run_modify]

theorem bernoulli_spec (p : NNReal) (hp : p ≤ 1) (post : Bool → ENNReal) :
    ⦃ post true * p + post false * (1 - p) ⦄
      PMF.bernoulli p hp
    ⦃ post ⦄ := by
  rw [Triple.iff]
  change post true * (p : ENNReal) + post false * (1 - (p : ENNReal)) ≤
    expect (PMF.bernoulli p hp) post
  unfold expect
  rw [tsum_bool]
  simp [PMF.bernoulli_apply, mul_comm, add_comm]

theorem expect_maybeIncrementRun_reached (p : NNReal) (hp : p ≤ 1) (target n : Nat) :
    expect (maybeIncrementRun p hp n)
      (fun r : PUnit × Nat => if target ≤ r.2 then 1 else 0) =
      if target ≤ n then (1 : ENNReal) else if target ≤ n + 1 then p else 0 := by
  unfold maybeIncrementRun
  rw [expect_map]
  by_cases hn : target ≤ n
  · have hpost :
        (fun tick : Bool => if target ≤ (n + if tick then 1 else 0) then (1 : ENNReal) else 0) =
          fun _ => (1 : ENNReal) := by
      funext tick
      cases tick <;> simp [hn, Nat.le_trans hn (Nat.le_succ n)]
    rw [hpost, expect_const_one]
    simp [hn]
  · by_cases hsucc : target ≤ n + 1
    · unfold expect
      rw [tsum_bool]
      simp [PMF.bernoulli_apply, hn, hsucc]
    · unfold expect
      rw [tsum_bool]
      simp [PMF.bernoulli_apply, hn, hsucc]

theorem spec_maybeIncrement_reached (p : NNReal) (hp : p ≤ 1) (target : Nat) :
    ⦃ fun n => if target ≤ n then (1 : ENNReal) else if target ≤ n + 1 then p else 0 ⦄
      maybeIncrement p hp
    ⦃ fun _ n => if target ≤ n then 1 else 0 ⦄ := by
  rw [Triple.iff]
  intro n
  rw [StateT.apply_wp]
  rw [maybeIncrement_run, wp_apply, expect_maybeIncrementRun_reached]


end PMF
