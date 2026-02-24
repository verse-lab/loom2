import Loom.WP.Basic

open Lean.Order

namespace Loom

/-!
# Hoare triples

Hoare triples form the basis for compositional functional correctness proofs about monadic programs.

As usual, `Triple pre x post epost` holds iff the precondition `pre` entails the weakest
precondition `wp x post epost` of `x : m α` for the postcondition `post` and error
postcondition `epost`.
It is thus defined in terms of an instance `WPMonad m l e`.
-/

universe u v
variable {m : Type u → Type v} {l : Type u} {e : Type u}

/-- A Hoare triple for reasoning about monadic programs. A Hoare triple `Triple pre x post epost`
is a *specification* for `x`: if assertion `pre` holds before `x`, then postcondition `post` holds
after running `x` (and `epost` handles any errors). -/
inductive Triple [Monad m] [WPMonad m l e] (pre : l) (x : m α) (post : α → l) (epost : e) : Prop
  | intro (hwp : pre ⊑ wp x post epost)

namespace Triple

variable [Monad m] [WPMonad m l e]

/-- Unfold a Hoare triple to its definition as a weakest precondition entailment. -/
theorem iff {x : m α} {pre : l} {post : α → l} {epost : e} :
    Triple pre x post epost ↔ (pre ⊑ wp x post epost) :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

/-- The consequence rule: a Hoare triple is equivalent to the ability to strengthen the
precondition and weaken the postcondition. -/
theorem iff_conseq {x : m α} {pre : l} {post : α → l} {epost : e} :
    Triple pre x post epost ↔
    (∀ pre' post', (pre' ⊑ pre) → (post ⊑ post') → pre' ⊑ wp x post' epost) := by
  constructor
  · intro ⟨h⟩ pre' post' hpre hpost
    exact PartialOrder.rel_trans hpre (PartialOrder.rel_trans h (WPMonad.wp_cons x _ _ epost hpost))
  · intro h
    exact ⟨h _ _ PartialOrder.rel_refl (fun _ => PartialOrder.rel_refl)⟩

/-- Extract a wp entailment from a triple, strengthening the precondition and weakening the
postcondition. -/
theorem entails_wp_of_pre_post {x : m α} {pre pre' : l} {post post' : α → l} {epost : e}
    (h : Triple pre' x post' epost) (hpre : pre ⊑ pre') (hpost : post' ⊑ post) :
    pre ⊑ wp x post epost :=
  iff_conseq.mp h _ _ hpre hpost

/-- Extract a wp entailment from a triple, strengthening the precondition. -/
theorem entails_wp_of_pre {x : m α} {pre pre' : l} {post : α → l} {epost : e}
    (h : Triple pre' x post epost) (hpre : pre ⊑ pre') :
    pre ⊑ wp x post epost :=
  iff_conseq.mp h _ _ hpre (fun _ => PartialOrder.rel_refl)

/-- Extract a wp entailment from a triple, weakening the postcondition. -/
theorem entails_wp_of_post {x : m α} {pre : l} {post post' : α → l} {epost : e}
    (h : Triple pre x post' epost) (hpost : post' ⊑ post) :
    pre ⊑ wp x post epost :=
  iff_conseq.mp h _ _ PartialOrder.rel_refl hpost

/-- Hoare triple for `pure`: if `pre ⊑ post a`, then `pure a` satisfies the triple. -/
theorem pure (a : α) (h : pre ⊑ post a) :
    Triple pre (pure (f := m) a) post epost :=
  iff.mpr (PartialOrder.rel_trans h (WPMonad.wp_pure a post epost))

/-- Hoare triple for `bind`: if `x` establishes an intermediate postcondition `mid`, and for every
result `a`, `f a` takes `mid a` to the final postcondition `post`, then `x >>= f` takes `pre` to
`post`. -/
theorem bind (x : m α) (f : α → m β)
    (mid : α → l)
    (hx : Triple pre x mid epost)
    (hf : ∀ a, Triple (mid a) (f a) post epost) :
    Triple pre (x >>= f) post epost := by
  apply iff.mpr
  apply PartialOrder.rel_trans (iff.mp hx)
  apply PartialOrder.rel_trans (WPMonad.wp_cons x mid (fun a => wp (f a) post epost) epost
    (fun a => iff.mp (hf a)))
  exact WPMonad.wp_bind x f post epost

/-!
## Not yet ported: `Triple.and` and `Triple.mp`

These require a **conjunctivity** axiom for `wp`:

    wp x (fun a => post₁ a ⊓ post₂ a) epost = wp x post₁ epost ⊓ wp x post₂ epost

i.e., the weakest precondition distributes over binary meet of postconditions.

With this axiom, `Triple.and` (combining two triples for the same program into a conjunction)
and `Triple.mp` (modus ponens on triples) can be proved following Std/Do/Triple/Basic.lean.

To port them, either:
1. Add `wp_conj` as an axiom to `WPMonad`, or
2. Define a subclass `ConjunctiveWPMonad` extending `WPMonad` with the conjunctivity property.

In Std/Do, conjunctivity is built into `PredTrans` (every predicate transformer carries a proof
of `Conjunctive`), so it is always available. In our framework, `wp_cons` (monotonicity) is the
only structural property, which suffices for the consequence rule but not for conjunction.
-/

end Triple

end Loom
