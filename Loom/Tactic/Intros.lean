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

/-! ## InvListWithNames: named conjunction list -/

/-- Named conjunction — `one name p` is just `p`, `cons name p rest` is `p ∧ rest`.
    NOT reducible so `simp` doesn't unfold it. VCGen detects and decomposes explicitly. -/
noncomputable def InvListWithNames.one (_name : Lean.Name) (p : Prop) : Prop := p
noncomputable def InvListWithNames.cons (_name : Lean.Name) (p : Prop) (rest : Prop) : Prop := p ∧ rest

-- Pre-intro rules for VCGen
theorem invlist_cons_pre_intro (_name : Lean.Name) (p rest c : Prop) :
    (p → rest ⊑ c) → InvListWithNames.cons _name p rest ⊑ c := by
  unfold InvListWithNames.cons
  intro h ⟨hp, hr⟩; exact h hp hr

theorem invlist_one_pre_intro (_name : Lean.Name) (p c : Prop) :
    (p → True ⊑ c) → InvListWithNames.one _name p ⊑ c := by
  unfold InvListWithNames.one
  intro h hp; exact h hp trivial

/-! ## Name extraction from Expr -/

/-- Extract a `Name` from an `Expr` representing a `Lean.Name` value.
    Handles `Name.str .anonymous "str"` and `Name.mkSimple "str"`. -/
def exprToName? (e : Expr) : Option Name :=
  match e.app2? ``Lean.Name.str with
  | some (_, strExpr) =>
    match strExpr with
    | .lit (.strVal s) => some (Name.mkSimple s)
    | _ => none
  | none =>
    match e.app1? ``Lean.Name.mkSimple with
    | some strExpr =>
      match strExpr with
      | .lit (.strVal s) => some (Name.mkSimple s)
      | _ => none
    | none => none

/-! ## MProd splitting lemmas -/

theorem MProd.forall_intro {α : Type u} {β : Type u} {p : MProd α β → Prop} :
    (∀ x y, p ⟨x, y⟩) → (∀ xy, p xy) :=
  fun h ⟨a, b⟩ => h a b

theorem MProd.fst_eq {α : Type u} {β : Type u} (a : α) (b : β) :
    (MProd.mk a b).fst = a := rfl

theorem MProd.snd_eq {α : Type u} {β : Type u} (a : α) (b : β) :
    (MProd.mk a b).snd = b := rfl

/-! ## Name hints for VCGen -/

/-- Thread-local storage for MProd component names, set by `prove_correct`
    before `mvcgen'` runs. -/
initialize mProdNameHintsRef : IO.Ref (Array Name) ← IO.mkRef #[]

/-- Clause name hints for hypothesis naming in `introMeetPre`. -/
structure ClauseNameHints where
  preNames  : Array Name := #[]  -- names for require clauses (pre-conditions)
  postNames : Array Name := #[]  -- names for ensures clauses (post-conditions)
  invNames  : Array Name := #[]  -- names for invariant clauses
  deriving Inhabited

initialize clauseNameHintsRef : IO.Ref ClauseNameHints ← IO.mkRef {}

/-! ## VCGen intro procedures

Procedures for introducing variables and hypotheses when unfolding Triples
and handling preconditions in VCGen goals.
-/

/-- Cached backward rules for intro procedures. -/
structure IntroRules where
  tripleIntro        : BackwardRule
  meetPreIntro       : BackwardRule
  trueMeetPreElim    : BackwardRule
  propPreIntro       : BackwardRule
  mProdForall        : BackwardRule
  invlistConsPreIntro : BackwardRule
  invlistOnePreIntro  : BackwardRule

/-- Build the `IntroRules` cache. -/
def IntroRules.mk' : SymM IntroRules := do
  return {
    tripleIntro        := ← mkBackwardRuleFromDecl ``Triple.intro
    meetPreIntro       := ← mkBackwardRuleFromDecl ``meet_pre_intro'
    trueMeetPreElim    := ← mkBackwardRuleFromDecl ``true_meet_pre_elim
    propPreIntro       := ← mkBackwardRuleFromDecl ``prop_pre_intro
    mProdForall        := ← mkBackwardRuleFromDecl ``MProd.forall_intro
    invlistConsPreIntro := ← mkBackwardRuleFromDecl ``invlist_cons_pre_intro
    invlistOnePreIntro  := ← mkBackwardRuleFromDecl ``invlist_one_pre_intro
  }

/-- Extract MProd component names from a `forIn` callback expression.
    The callback has shape `fun x r => have i := r.fst; have rest := r.snd; have j := rest.fst; ...`.
    Returns the names `[i, j, k, ...]` in order. -/
private partial def extractMProdNamesFromCallback (e : Expr) : MetaM (Array Name) := do
  -- Walk through lambdas to find the body
  Meta.lambdaTelescope e fun _args body => do
    -- The body starts with let-bindings that unpack the MProd:
    --   have i := r.fst;     -- component name (value accesses .fst)
    --   have x := r.snd;     -- intermediate tuple (value accesses .snd, type is MProd)
    --   have j := x.fst;     -- component name
    --   have k := x.snd;     -- last component (no more nesting)
    -- We collect names where the let-value accesses .fst or is the final .snd
    -- Simple heuristic: skip names whose type is MProd (those are intermediates)
    let mut names : Array Name := #[]
    let mut cur := body
    while cur.isLet do
      let ty := cur.letType!
      unless ty.isAppOfArity ``MProd 2 do
        names := names.push cur.letName!
      cur := cur.letBody!
    return names

/-- Extract MProd component names from a definition by finding its `forIn` callback.
    Searches the definition body for `ForIn.forIn ... callback` pattern. -/
def extractMProdNamesFromDef (defName : Name) : MetaM (Array Name) := do
  let some ci := (← getEnv).find? defName | return #[]
  let some val := ci.value? | return #[]
  -- Search for forIn applications and extract names from the callback
  let mut result : Array Name := #[]
  -- Use Expr.find? to locate forIn
  -- Find any ForIn.forIn application
  if let some forInExpr := val.find? (fun e => e.getAppFn.isConstOf ``ForIn.forIn) then
    -- The callback is always the last argument
    let args := forInExpr.getAppArgs
    let callback := args.back!
    result ← extractMProdNamesFromCallback callback
  return result
/-- Split MProd forall binders, using `nameHints` for proper variable naming.
    `nameHints` should contain the original mutable variable names (e.g., `[i, j, k]`). -/
partial def splitMProdForalls (rules : IntroRules) (nameHints : Array Name := #[])
    (goal : Grind.Goal) : SymM Grind.Goal := do
  -- Instantiate mvars and fold kernel projections
  let mut mvarId := goal.mvarId
  let mut type ← instantiateMVars (← mvarId.getType)
  let type' ← Grind.foldProjs type
  if type' != type then type := type'
  if type != (← mvarId.getType) then
    mvarId ← mvarId.replaceTargetDefEq type
  unless type.isForall do return { goal with mvarId }
  if type.bindingDomain!.isAppOfArity ``MProd 2 then
    -- Use name hint if available, otherwise fall back to binding name
    let fstName := if nameHints.size > 0 then nameHints[0]! else type.bindingName!
    let remainingHints := if nameHints.size > 0 then nameHints.extract 1 nameHints.size else #[]
    -- Apply MProd.forall_intro: ∀ (r : MProd A B), P r → ∀ (x : A) (y : B), P ⟨x, y⟩
    let ci ← getConstInfo ``MProd.forall_intro
    let us ← ci.levelParams.mapM fun _ => mkFreshLevelMVar
    let subgoals ← mvarId.apply (mkConst ``MProd.forall_intro us)
    let [mvarId'] := subgoals | return { goal with mvarId }
    -- Intro the first component with the proper name
    let (_, mvarId'') ← mvarId'.intro fstName
    splitMProdForalls rules remainingHints { goal with mvarId := mvarId'' }
  else
    -- Use name hint if this binder was an MProd component (e.g., the last element
    -- after all MProd splits), otherwise use the original binding name
    let name := if nameHints.size > 0 then nameHints[0]! else type.bindingName!
    let remainingHints := if nameHints.size > 0 then nameHints.extract 1 nameHints.size else #[]
    let (_, mvarId') ← mvarId.intro name
    splitMProdForalls rules remainingHints { goal with mvarId := mvarId' }

/-- Introduce all forall-bound variables, splitting MProd binders and
    simplifying `⟨x, y⟩.fst → x`, `⟨x, y⟩.snd → y` afterwards.
    Threads `Simp.State` for cache persistence across calls. -/
def introsWP (rules : IntroRules) (simpMethods? : Option Sym.Simp.Methods)
    (nameHints : Array Name := #[]) (goal : Grind.Goal) : GrindM Grind.Goal := do
  let mut goal := goal
  goal ← splitMProdForalls rules nameHints goal
  if let some methods := simpMethods? then
    -- Fold kernel projections (Expr.proj → app form) in target and hypotheses
    let mut mvarId := goal.mvarId
    let target ← mvarId.getType
    let target' ← Grind.foldProjs target
    if target != target' then
      mvarId ← mvarId.replaceTargetDefEq target'
    -- Fold in hypotheses
    mvarId ← mvarId.withContext do
      let lctx ← getLCtx
      let mut mid := mvarId
      for ldecl in lctx do
        if ldecl.isImplementationDetail then continue
        let ty := ldecl.type
        let ty' ← Grind.foldProjs ty
        if ty != ty' then
          mid ← mid.changeLocalDecl ldecl.fvarId ty'
      return mid
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

/-- Recursively decompose a precondition `pre ⊑ rhs` by introducing
    individual components as hypotheses. Handles:
    - `meet` (conjunction): `a ⊓ b ⊑ c` → intro right, recurse on left
    - `InvListWithNames.cons`: extract name from the constructor, intro with name
    - `InvListWithNames.one`: extract name, intro, done
    - `True ⊓ b`: skip True
    - Non-meet, non-True: intro as a single hypothesis -/
meta partial def introMeetPre (rules : IntroRules) (goal : MVarId) : SymM MVarId :=
  goal.withContext do
  let type ← goal.getType
  let_expr PartialOrder.rel _α _inst pre _rhs := type | return goal
  -- InvListWithNames.cons name p rest ⊑ c
  if pre.isAppOfArity ``InvListWithNames.cons 3 then
    let nameExpr := pre.getAppArgs[0]!
    let hypName := exprToName? nameExpr |>.getD `h
    match ← rules.invlistConsPreIntro.apply goal with
    | .goals [goal'] =>
      let (_, goal'') ← goal'.intro hypName
      introMeetPre rules goal''
    | _ => return goal
  -- InvListWithNames.one name p ⊑ c
  else if pre.isAppOfArity ``InvListWithNames.one 2 then
    let nameExpr := pre.getAppArgs[0]!
    let hypName := exprToName? nameExpr |>.getD `h
    match ← rules.invlistOnePreIntro.apply goal with
    | .goals [goal'] =>
      let (_, goal'') ← goal'.intro hypName
      return goal''
    | _ => return goal
  -- meet (conjunction)
  else if pre.isAppOf ``meet && pre.getAppNumArgs ≥ 4 then
    let a := pre.getAppArgs[2]!
    if a.isConstOf ``True then
      match ← rules.trueMeetPreElim.apply goal with
      | .goals [goal'] => introMeetPre rules goal'
      | _ => return goal
    else
      match ← rules.meetPreIntro.apply goal with
      | .goals [goal'] =>
        let .goal _ goal'' ← Sym.intros goal' | return goal'
        introMeetPre rules goal''
      | _ => return goal
  -- Non-meet, non-True: single prop
  else if !pre.isConstOf ``True then
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
