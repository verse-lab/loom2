/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
import Lean
import Loom.Tactic.ShareExt
import Loom.Triple.Basic

open Lean Parser Meta Elab Tactic Sym Loom Lean.Order Grind
open Std.Do'

namespace Loom

/-! ## MProd splitting lemmas -/

theorem MProd.forall_intro {α : Type u} {β : Type u} {p : MProd α β → Prop} :
    (∀ x y, p ⟨x, y⟩) → (∀ xy, p xy) :=
  fun h ⟨a, b⟩ => h a b

theorem MProd.fst_eq {α : Type u} {β : Type u} (a : α) (b : β) :
    (MProd.mk a b).fst = a := rfl

theorem MProd.snd_eq {α : Type u} {β : Type u} (a : α) (b : β) :
    (MProd.mk a b).snd = b := rfl

/-! ## VCGen intro procedures

Procedures for introducing variables and hypotheses when unfolding Triples
and handling preconditions in VCGen goals.
-/

/-- Cached backward rules for intro procedures. -/
structure IntroRules where
  tripleIntro     : BackwardRule
  meetPreIntro    : BackwardRule
  trueMeetPreElim : BackwardRule
  propPreIntro    : BackwardRule
  mProdForall     : BackwardRule

/-- Build the `IntroRules` cache. -/
def IntroRules.mk' : SymM IntroRules := do
  return {
    tripleIntro     := ← mkBackwardRuleFromDecl ``Triple.intro
    meetPreIntro    := ← mkBackwardRuleFromDecl ``meet_pre_intro'
    trueMeetPreElim := ← mkBackwardRuleFromDecl ``true_meet_pre_elim
    propPreIntro    := ← mkBackwardRuleFromDecl ``prop_pre_intro
    mProdForall     := ← mkBackwardRuleFromDecl ``MProd.forall_intro
  }

/-- Introduce all forall binders one-by-one, splitting any `MProd`-typed ones.
    For `∀ (s : MProd A (MProd B C)), P s`:
    1. Outermost is MProd → apply split rule → `∀ (a : A) (bc : MProd B C), P ⟨a, bc⟩`
    2. Intro `a` (non-MProd) via `goal.intros #[name]`
    3. Outermost is MProd again → split → `∀ (b : B) (c : C), P ⟨a, ⟨b, c⟩⟩`
    4. Intro `b`, intro `c` -/
partial def splitMProdForalls (rules : IntroRules) (goal : Grind.Goal) : SymM Grind.Goal := do
  -- Instantiate mvars so the type is fully resolved after prior apply/intro steps
  let mut mvarId := goal.mvarId
  let type ← instantiateMVars (← mvarId.getType)
  if type != (← mvarId.getType) then
    mvarId ← mvarId.replaceTargetDefEq type
  unless type.isForall do return { goal with mvarId }
  if type.bindingDomain!.isAppOfArity ``MProd 2 then
    -- Use Meta.apply instead of BackwardRule.apply to avoid introN issues
    let ci ← getConstInfo ``MProd.forall_intro
    let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
    let subgoals ← mvarId.apply (mkConst ``MProd.forall_intro us)
    let [mvarId'] := subgoals | return { goal with mvarId }
    splitMProdForalls rules { goal with mvarId := mvarId' }
  else
    let (_, mvarId') ← mvarId.intro type.bindingName!
    splitMProdForalls rules { goal with mvarId := mvarId' }

/-- Introduce all forall-bound variables, splitting MProd binders and
    simplifying `⟨x, y⟩.fst → x`, `⟨x, y⟩.snd → y` afterwards.
    Threads `Simp.State` for cache persistence across calls. -/
def introsWP (rules : IntroRules) (simpMethods? : Option Sym.Simp.Methods)
    (goal : Grind.Goal) : GrindM Grind.Goal := do
  let mut goal := goal
  goal ← splitMProdForalls rules goal
  if let some methods := simpMethods? then
    -- Fold kernel projections (Expr.proj → app form) before Sym.simp
    let mut mvarId := goal.mvarId
    let target ← mvarId.getType
    let target' ← Grind.foldProjs target
    if target != target' then
      mvarId ← mvarId.replaceTargetDefEq target'
    goal := { goal with mvarId }
    let simpResult ← goal.simp methods
    match simpResult with
    | .goal goal' => goal := goal'
    | .closed | .noProgress => pure ()
  return goal

/-- Expand `pre ⊑ rhs` when the lattice type is a function type `σ₁ → ... → σₙ → BaseTy`
    into `∀ s₁ ... sₙ, pre s₁ ... sₙ ⊑ rhs s₁ ... sₙ`, then intro the `sᵢ`.
    This is needed after unfolding Triple when `Pred` has excess state arguments. -/
meta def introsExcessArgs (goal : Grind.Goal) : SymM Grind.Goal := goal.withContext do
  let type ← goal.mvarId.getType
  let_expr PartialOrder.rel α _inst pre rhs := type | return goal
  unless α.isForall do return goal
  -- Build ∀ (s₁ : σ₁) ... (sₙ : σₙ), (pre s₁ ... sₙ) ⊑ (rhs s₁ ... sₙ)
  let newTarget ← liftMetaM <| Meta.forallTelescope α fun ss _baseTy => do
    let preApplied := mkAppN pre ss
    let rhsApplied := mkAppN rhs ss
    let innerRel ← mkAppM ``PartialOrder.rel #[preApplied, rhsApplied]
    mkForallFVars ss innerRel
  let newTarget ← shareCommon newTarget
  let goalMVarId ← goal.mvarId.replaceTargetDefEq newTarget
  let goal := { goal with mvarId := goalMVarId }
  let .goal _ goal' ← goal.intros #[] | return goal
  return goal'

/-- Recursively decompose a meet precondition `a ⊓ b ⊑ c` by introducing
    individual components as hypotheses. Uses:
    - `meet_pre_intro`: `(a → b ⊑ c) → a ⊓ b ⊑ c` — intro left component
    - `true_meet_pre_elim`: `b ⊑ c → True ⊓ b ⊑ c` — skip True
    - `prop_pre_intro`: `(x → True ⊑ y) → x ⊑ y` — base case (non-met pre) -/
meta partial def introMeetPre (rules : IntroRules) (goal : MVarId) : SymM MVarId :=
  goal.withContext do
  let type ← goal.getType
  let_expr PartialOrder.rel _α _inst pre _rhs := type | return goal
  -- Check if pre is a meet
  if pre.isAppOf ``meet && pre.getAppNumArgs ≥ 4 then
    let a := pre.getAppArgs[2]!
    if a.isConstOf ``True then
      -- True ⊓ b ⊑ c  →  b ⊑ c
      match ← rules.trueMeetPreElim.apply goal with
      | .goals [goal'] => introMeetPre rules goal'
      | _ => return goal
    else
      -- a ⊓ b ⊑ c  →  a → b ⊑ c
      match ← rules.meetPreIntro.apply goal with
      | .goals [goal'] =>
        let .goal _ goal'' ← Sym.intros goal' | return goal'
        introMeetPre rules goal''
      | _ => return goal
  else if !pre.isConstOf ``True then
    -- Non-meet, non-True pre: apply prop_pre_intro to get `pre → True ⊑ rhs`
    match ← rules.propPreIntro.apply goal with
    | .goals [goal'] =>
      let .goal _ goal'' ← Sym.intros goal' | return goal'
      return goal''
    | _ => return goal
  else
    return goal

/-- Unfold `⦃P⦄ x ⦃Q⦄` into `P ⊑ wp⟦x⟧ Q`, expanding excess state args and introing.
    Returns the original goal if not a Triple. -/
meta def unfoldTriple (rules : IntroRules) (goal : Grind.Goal) : SymM Grind.Goal :=
  goal.withContext do
  let type ← goal.mvarId.getType
  unless type.isAppOf ``Triple do return goal
  match ← goal.apply rules.tripleIntro with
  | .goals [goal'] => introsExcessArgs goal'
  | _ => return goal

end Loom
