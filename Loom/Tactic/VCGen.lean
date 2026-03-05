import Lean
import Loom.Tactic.Attr
import Loom.Triple.Basic
import Loom.Triple.SpecLemmas
import Loom.WP.SimpLemmas
import Loom.Frame
import Lean.Meta
import Lean.Meta.Match.Rewrite
import Loom.Tactic.ShareExt

open Lean Parser Meta Elab Tactic Sym Loom Lean.Order
open Loom.Tactic.SpecAttr

namespace Loom

initialize registerTraceClass `Loom.Tactic.vcgen

namespace Loom.Tactic.SpecAttr

/--
Look up `SpecTheorem`s in the `@[lspec]` database.
Takes all specs that match the given program `e` and sorts by descending priority.
-/
def SpecTheorems.findSpecs (database : SpecTheorems) (e : Expr) : MetaM (Array SpecTheorem) := do
  let candidates ← database.specs.getMatch e
  let candidates := candidates.filter (!database.erased.contains ·.proof)
  return candidates.qsort (·.priority > ·.priority)

end Loom.Tactic.SpecAttr

/-- Count function arrows in a type, e.g. `σ1 → σ2 → Prop` → 2 -/
private partial def countExcessArgs (l : Expr) : MetaM Nat := do
  let l ← whnfR l
  if l.isForall then return 1 + (← countExcessArgs l.bindingBody!)
  else return 0

/-- Extract the argument types from function arrows of a type -/
private def getExcessArgTypes (l : Expr) (n : Nat) : MetaM (Array Expr) := do
  let mut result := #[]
  let mut l := l
  for _ in [:n] do
    l ← whnfR l
    result := result.push l.bindingDomain!
    l := l.bindingBody!
  return result

def preprocessExpr (e : Expr) : SymM Expr := do
  shareCommon (← unfoldReducible (← instantiateMVars e))

private def withNameHead? (e : Expr) : Option (Array Expr) :=
  let e := e.consumeMData
  if e.isAppOf ``withName then
    some e.getAppArgs
  else
    none

private def evalNameExpr? (e : Expr) : MetaM (Option Name) := do
  try
    return some (← Lean.Meta.reduceEval e)
  catch _ =>
    return none

/--
Introduce exactly one binder. If the binder domain is of shape `withName n x`,
introduce it using name `n`; otherwise fall back to regular `introN 1`.
-/
private def intro1WithName (mvarId : MVarId) : SymM IntrosResult := do
  let type ← mvarId.getType
  let .forallE info domain tp body := type | return .failed
  let some args := withNameHead? domain
    | introN mvarId 1
  if h : args.size > 2 then
    let some n ← evalNameExpr? args[0]
      | return (← introN mvarId 1)
    let domain <- mkAppNS args[2] (args.drop 3)
    let type <- share <| Expr.forallE info domain tp body
    Sym.intros (← mvarId.replaceTargetDefEq type) #[n]
  else
    introN mvarId 1

/--
Check definitional equality without committing metavariable assignments.
Useful for "can these unify?" probes when matching candidate specs.
-/
private def isDefEqNoAssign (a b : Expr) : MetaM Bool := do
  withoutModifyingState <| isDefEqGuarded a b

/-- Rebuild a fully-applied `wp` application with replaced `post`/`epost` arguments. -/
private def mkWpWithPostEPost (rhs post epost : Expr) : MetaM Expr := do
  unless rhs.isAppOfArity ``wp 9 do
    throwError "target not a wp application {rhs}"
  return rhs.getAppArgs.take 7
    |>.push post
    |>.push epost
    |> mkAppN rhs.getAppFn

/-- Build the explicit pointwise implication premise used to weaken a concrete `post`. -/
private def mkPostPointwisePremise (postSpec postTarget postTy : Expr) (ssTypes : Array Expr) : SymM Expr := do
  let .forallE _ α _ _ := postTy
    | throwError "expected a postcondition function, got {indentExpr postTy}"
  withLocalDeclD `a α fun a => do
  withLocalDeclsDND (ssTypes.map (`s, ·)) fun ss' => do
    let lhs := mkAppN (mkApp postSpec a) ss'
    let rhs := mkAppN (mkApp postTarget a) ss'
    mkForallFVars (#[a] ++ ss') (← mkArrow lhs rhs)

/--
Turn a spec proof `pre ⊑ wp prog post epost` into an explicit implication-shaped proof term.

If `post` and/or `epost` are concrete (not top-level metavariables), fresh target metavariables
are introduced and the proof is generalized using `WPMonad.wp_cons`, `WPMonad.wp_econs`,
or `WPMonad.wp_cons_econs`.
-/
private def mkSpecBackwardProof
    (pre rhs specProof : Expr) (ss ssTypes : Array Expr) : SymM Expr := do
  let_expr wp _m _l _e _monadInst _instWP _α prog postSpec epostSpec := rhs
    | throwError "target not a wp application {rhs}"
  let preApplied := mkAppN pre ss
  let specApplied := mkAppN specProof ss
  let postAbstract := postSpec.consumeMData.isMVar
  let epostAbstract := epostSpec.consumeMData.isMVar
  match postAbstract, epostAbstract with
  | true, true =>
      let proofType ← mkArrow preApplied (mkAppN rhs ss)
      mkExpectedTypeHint (mkAppN specProof ss) proofType
  | false, true =>
    let postTy ← Sym.inferType postSpec
    let postTarget ← mkFreshExprMVar (userName := `post) postTy
    let hpostTy ← mkPostPointwisePremise postSpec postTarget postTy ssTypes
    withLocalDeclD `hpost hpostTy fun hpost => do
      withLocalDeclD `hpre preApplied fun hpre => do
        let base := mkApp specApplied hpre
        let hpostRelTy ← mkAppM ``PartialOrder.rel #[postSpec, postTarget]
        let hpostRel ← mkExpectedTypeHint hpost hpostRelTy
        let mono ← mkAppM ``WPMonad.wp_cons #[prog, postSpec, postTarget, epostSpec, hpostRel]
        let body := mkApp (mkAppN mono ss) base
        mkLambdaFVars #[hpost, hpre] body
  | true, false =>
    let epostTarget ← mkFreshExprMVar (userName := `epost) (← Sym.inferType epostSpec)
    let hepostTy ← mkAppM ``PartialOrder.rel #[epostSpec, epostTarget]
    withLocalDeclD `hepost hepostTy fun hepost => do
      withLocalDeclD `hpre preApplied fun hpre => do
        let base := mkApp specApplied hpre
        let mono ← mkAppM ``WPMonad.wp_econs #[prog, postSpec, epostSpec, epostTarget, hepost]
        let body := mkApp (mkAppN mono ss) base
        mkLambdaFVars #[hepost, hpre] body
  | false, false =>
    let postTy ← Sym.inferType postSpec
    let postTarget ← mkFreshExprMVar (userName := `post) postTy
    let epostTarget ← mkFreshExprMVar (userName := `epost) (← Sym.inferType epostSpec)
    let hpostTy ← mkPostPointwisePremise postSpec postTarget postTy ss
    let hepostTy ← mkAppM ``PartialOrder.rel #[epostSpec, epostTarget]
    withLocalDeclD `hpost hpostTy fun hpost => do
      withLocalDeclD `hepost hepostTy fun hepost => do
        withLocalDeclD `hpre preApplied fun hpre => do
          let base := mkApp specApplied hpre
          let hpostRelTy ← mkAppM ``PartialOrder.rel #[postSpec, postTarget]
          let hpostRel ← mkExpectedTypeHint hpost hpostRelTy
          let mono ← mkAppM ``WPMonad.wp_cons_econs
            #[prog, postSpec, postTarget, epostSpec, epostTarget, hpostRel, hepost]
          let body := mkApp (mkAppN mono ss) base
          mkLambdaFVars #[hpost, hepost, hpre] body


/-
  -- Create fresh metavars for excess state args (abstractMVars will bind them as ∀)
  let ss ← excessArgs.mapM fun arg => do
    mkFreshExprMVar (userName := `s) <| ← Sym.inferType arg
  -- Build: pre s1 ... sn → wp prog post epost s1 ... sn
  -- Using mkExpectedTypeHint because PartialOrder.rel is a projection that
  -- unfoldReducible/mkPatternFromType cannot see through structurally
  let proofType ← mkArrow (mkAppN pre ss) (mkAppN rhs ss)
  let spec ← mkExpectedTypeHint (mkAppN specProof ss) proofType
-/

/--
Try to build a backward rule from a single spec theorem in `⊑` form.

Given a spec `pre ⊑ wp prog post epost` where the lattice type is
`l = σ1 → ... → σn → Prop`, produces an auxiliary lemma of the form
`∀ s1 ... sn, pre s1 ... sn → wp prog post epost s1 ... sn`.

This conversion is necessary because `PartialOrder.rel` is a projection (not unfolded
by `unfoldReducible`), so `mkPatternFromType` cannot structurally see the `→`. We
explicitly construct an implication-shaped proof term, adding `wp_cons`/`wp_econs`
premises when the spec uses concrete `post`/`epost`.

- `l`: the goal's lattice type (e.g. `Nat → Prop`)
- `instWP`: the `WPMonad` instance for the goal monad; matching against the spec's
  instance transitively unifies `m`, `e`, and `monadInst`
- `excessArgs`: free variables representing state args from `l = σ1 → ... → σn → Prop`;
  fresh metavariables are created for these so that `abstractMVars` can abstract them
  alongside the spec's universally quantified parameters
-/
def tryMkBackwardRuleFromSpec (specThm : SpecTheorem)
  (e l instWP : Expr) (excessArgs : Array Expr) : OptionT SymM BackwardRule := do
  -- dbg_trace s!"tryMkBackwardRuleFromSpec: instWP = {← ppExpr instWP}"
  -- Instantiate the spec theorem, creating metavars for all universally quantified params
  let (_xs, _bs, specProof, specType) ← specThm.proof.instantiate
  let_expr PartialOrder.rel l' _cl' pre rhs := specType
    | throwError "target not a partial order ⊑ application {specType}"
  -- Use isDefEqGuarded (not isDefEqS) because isDefEqS is a lightweight structural check
  -- that may fail to see through abbreviations like `Unit := PUnit`
  guard <| ← isDefEqGuarded l l'
  let_expr wp _m' _ _ _monadInst' instWP' _α e' _post _epost := rhs
    | throwError "target not a wp application {rhs}"
  -- Unifying instWP transitively assigns m, e, cl, monadInst via type-level unification.
  -- For e/e' we only probe that unification exists, without committing assignments.
  guard <| ← isDefEqGuarded instWP instWP' <&&> isDefEqNoAssign e e'
  -- Use local excess-state binders so explicit post premises can be re-lifted to `⊑`.
  let mut ss := #[]
  let mut ssTypes := #[]
  for arg in excessArgs do
    let ty ← Sym.inferType arg
    ssTypes := ssTypes.push ty
    ss := ss.push <| ← mkFreshExprMVar (userName := `s) ty
  -- let ss ← excessArgs.mapM fun arg => do
  --   let ty ← Sym.inferType arg
  --   return (ty, ← mkFreshExprMVar (userName := `s) ty)
  let spec ← mkSpecBackwardProof pre rhs specProof ss ssTypes
  -- Abstract all remaining metavars (spec params + excess args) into an aux lemma
  let res ← abstractMVars spec
  let type ← preprocessExpr (← Meta.inferType res.expr)
  let spec ← Meta.mkAuxLemma res.paramNames.toList type res.expr
  mkBackwardRuleFromDecl spec

open Lean.Elab.Tactic.Do in
/--
Creates a reusable backward rule for `ite`. It proves a theorem of the following form:
```
example {m} {σ} {l} {e} [WPMonad m l e] -- These are fixed. The other arguments are parameters of the rule:
  {α} {c : Prop} [Decidable c] {t e : m α} {s₁ s₂ ... : σ} {pre : l} {post : α → l} {epost : e}
  (hthen : wp t post epost s₁ s₂ ...) (helse : wp e post epost s₁ s₂ ...)
  : wp (ite c t e) post epost s₁ s₂ ...
```
-/
meta def mkBackwardRuleForIte
    (wpHead m l errTy monadInst instWP : Expr)
    (excessArgs : Array Expr) : SymM BackwardRule := do
  let mTy ← Sym.inferType m
  let some aTy := if mTy.isForall then some mTy.bindingDomain! else none
    | throwError "Expected monad type constructor at {indentExpr m}"
  let prf ← withLocalDeclD `a aTy fun a => do
    let ma ← shareCommon <| mkApp m a
    withLocalDeclD `c (mkSort 0) fun c => do
    withLocalDeclD `dec (mkApp (mkConst ``Decidable) c) fun dec => do
    withLocalDeclD `t ma fun t => do
    withLocalDeclD `e ma fun e => do
    let maTy ← Sym.inferType ma
    let v ←
      match maTy with
      | .sort lvl => pure lvl
      | _ => throwError "Expected sort for type {indentExpr maTy}"
    let prog ← shareCommon (mkApp5 (mkConst ``ite [v]) ma c dec t e)
    let excessArgNamesTypes ← excessArgs.mapM fun arg =>
      return (`s, ← Sym.inferType arg)
    withLocalDeclsDND excessArgNamesTypes fun ss => do
    withLocalDeclD `post (← shareCommon (← mkArrow a l)) fun post => do
    withLocalDeclD `epost errTy fun epost => do
    let goalWithProg (prog : Expr) :=
      mkAppN (mkAppN wpHead #[m, l, errTy, monadInst, instWP, a, prog, post, epost]) ss
    let thenType ← mkArrow c (goalWithProg t)
    withLocalDeclD `hthen (← shareCommon thenType) fun hthen => do
    let elseType ← mkArrow (mkNot c) (goalWithProg e)
    withLocalDeclD `helse (← shareCommon elseType) fun helse => do
    let onAlt (hc : Expr) (hcase : Expr) := do
      let res ← rwIfWith hc prog
      if res.proof?.isNone then
        throwError "`rwIfWith` failed to rewrite {indentExpr prog}."
      let context ← withLocalDecl `x .default ma fun x => mkLambdaFVars #[x] (goalWithProg x)
      let res ← Simp.mkCongrArg context res
      res.mkEqMPR hcase
    let ht ← withLocalDecl `h .default c fun h => do
      mkLambdaFVars #[h] (← onAlt h (mkApp hthen h))
    let he ← withLocalDecl `h .default (mkNot c) fun h => do
      mkLambdaFVars #[h] (← onAlt h (mkApp helse h))
    let goalTy := goalWithProg prog
    let goalTySort ← Sym.inferType goalTy
    let u ←
      match goalTySort with
      | .sort lvl => pure lvl
      | _ => throwError "Expected sort for type {indentExpr goalTySort}"
    let prf := mkApp5 (mkConst ``dite [u]) goalTy c dec ht he
    mkLambdaFVars (#[a, c, dec, t, e] ++ ss ++ #[post, epost, hthen, helse]) prf
  let res ← abstractMVars prf
  let type ← preprocessExpr (← Sym.inferType res.expr)
  let prf ← Meta.mkAuxLemma res.paramNames.toList type res.expr
  mkBackwardRuleFromDecl prf

inductive LogicOp where
  | And
  | Imp
  -- Temporarily disabled:
  -- | Forall (n : Name)

/-- Map lattice connective declaration names to supported `LogicOp`s. -/
def _root_.Lean.Name.toLogicOp? : Name → Option LogicOp
  | ``meet => some .And
  | ``himp => some .Imp
  | _ => none

private def LogicOp.mkLatticeExpr (as : Array Expr) : LogicOp → MetaM Expr
  | .And => mkAppM ``meet as
  | .Imp => mkAppM ``himp as

/-- Lift an equality `lhs = rhs` to `(lhs args...) = (rhs args...)`. -/
private def liftEqByArgs (eqPrf : Expr) (args : List Expr) : MetaM Expr := do
  if args.isEmpty then
    return eqPrf
  let eqTy ← inferType eqPrf
  let some (_, lhs, _rhs) := eqTy.eq?
    | throwError "Expected equality proof, got {indentExpr eqTy}"
  let lhsTy ← inferType lhs
  let context ← withLocalDecl `x .default lhsTy fun x => do
    let app := mkAppN x args.toArray
    mkLambdaFVars #[x] app
  mkCongrArg context eqPrf

/--
Apply a function-extensional lemma (`*_fun_apply`) repeatedly over all excess
arguments, producing an equality at the fully applied level.

Example (`lop = .And`, `stepThm = ``meet_fun_apply`, `as = #[a, b]`,
`ss = [s₁, s₂]`): the resulting proof has type
`((a ⊓ b) s₁ s₂) = (a s₁ s₂ ⊓ b s₁ s₂)`.
-/
private partial def LogicOp.mkApplyEq
    (stepThm : Name) (lop : LogicOp)
    (as : Array Expr) (ss : List Expr) : MetaM Expr := do
  match ss with
  | [] => mkEqRefl =<< lop.mkLatticeExpr as
  | s :: ss' =>
    let step ← mkAppM stepThm <| as.push s
    if ss'.isEmpty then
      return step
    let stepLift ← liftEqByArgs step ss'
    let as := as.map (mkApp · s)
    let rest ← lop.mkApplyEq stepThm as ss'
    mkEqTrans stepLift rest

/-- Compute binder names/types used for fresh metavariables for logic operands. -/
private def mkArgNamesTypes (as : Array Expr) : SymM (Array (Name × Expr)) := do
  as.mapM fun arg => return (`s, ← Sym.inferType arg)

/-- Map a logic operator to its corresponding `*_fun_apply` lemma. -/
private def LogicOp.toApplyLemma : LogicOp → Name
  | .And => ``meet_fun_apply
  | .Imp => ``himp_fun_apply

/-- Map a logic operator to its corresponding proposition-level equivalence lemma. -/
private def LogicOp.toPropLemma : LogicOp → Name
  | .And => ``meet_prop_eq_and
  | .Imp => ``himp_prop_eq_imp

/--
Build:
1) `goal`: lattice expression applied to excess args,
2) `premise`: the corresponding proposition-level formula,
3) `eq`: proof `goal = premise`.
-/
private def LogicOp.mkGoalPremiseEq
    (lop : LogicOp) (as ss : Array Expr) : SymM (Expr × Expr × Expr) := do
  let applyLemma := lop.toApplyLemma
  let propLemma := lop.toPropLemma
  let lat ← lop.mkLatticeExpr as
  -- This is the final lattice-side goal `a ⊓ b s₁ ... sₙ` after applying excess state args.
  let goal ← shareCommon <| mkAppN lat ss
  -- Equality rewriting the lattice connective under all excess applications.
  let eqFun ← lop.mkApplyEq applyLemma as ss.toList
  -- Apply all excess args to each operand (`a s₁ .. sₙ`, `b s₁ .. sₙ`).
  let asApp := as.map (mkAppN · ss)
  -- Instantiate the proposition-level equivalence `a s₁ ... sₙ ⊓ b s₁ ... sₙ = a ∧ b s₁ ... sₙ` theorem for applied operands.
  let eqProp ← mkAppM propLemma asApp
  -- Extract the proposition-side RHS from the equality type: `a s₁ ... sₙ ⊓ b s₁ ... sₙ`
  let eqTy ← Sym.inferType eqProp
  let some (_, _lhsProp, rhsProp) := eqTy.eq?
    | throwError "Expected equality from {propLemma}, got {indentExpr eqTy}"
  -- Chain function-application rewriting with proposition equivalence.
  let eq ← mkEqTrans eqFun eqProp
  -- Return lattice goal, logical premise, and bridge equality.
  return (goal, rhsProp, eq)

/--
  Creates a reusable backward rule for a `CompleteLattice` logic expression.
  For example, if `lop` is `And`, then it creates a following theorem for fixed Complete Lattice `l` and
  its `[CompleteLattice l]` instance expression:

  ```
  -- `l` and `[CompleteLattice l]` are fixed
  theorem And_applied_intro (a : l) (b : l) s₁ : σ₁) (s₂ : σ₂) ... (sₙ : σₙ) :
    a s₁ ... sₙ ∧ b s₁ ... sₙ ->
    (a ⊓ b) s₁ ... sₙ
  ```
-/
def LogicOp.mkBackwardRuleForLogic (lop : LogicOp) (as : Array Expr) (excessArgs : Array Expr) : SymM BackwardRule := do

  -- Fresh metavariables become universally quantified after `abstractMVars`.
  let as ← as.mapM fun arg => do
    mkFreshExprMVar (userName := `a) (← Sym.inferType arg)
  let ss ← excessArgs.mapM fun arg => do
    mkFreshExprMVar (userName := `s) (← Sym.inferType arg)

  -- Build premise/goal bridge and turn it into `premise → goal`.
  let (goal, premise, eqGoalPremise) ← lop.mkGoalPremiseEq as ss
  let eqSymm ← mkEqSymm eqGoalPremise
  let prf ← mkAppM ``Eq.mp #[eqSymm]
  let prf ← mkExpectedTypeHint prf (← mkArrow premise goal)

  -- Abstract mvars, create an auxiliary declaration, and package as backward rule.
  let res ← abstractMVars prf
  let type ← preprocessExpr (← Meta.inferType res.expr)
  let prf ← Meta.mkAuxLemma res.paramNames.toList type res.expr
  mkBackwardRuleFromDecl prf

/--
Post-process a goal produced by `LogicOp.mkBackwardRuleForLogic`.
- `.And`: split `a ∧ b` into two subgoals using `And.intro`.
- `.Imp`: introduce one binder; if its domain is `withName n x`, use name `n`.
-/
def LogicOp.postProcessGoal (lop : LogicOp) (goal : MVarId) : SymM (List MVarId) := do
  match lop with
  | .And => do
    let rule ← mkBackwardRuleFromDecl ``And.intro
    let .goals goals ← rule.apply goal
      | throwError "Failed to apply And.intro to goal {goal.name}"
    return goals
  | .Imp => do
    let IntrosResult.goal _ goal ← intro1WithName goal
      | throwError "Failed to intro implication premise at goal {goal.name}"
    return [goal]

/--
Given an array of `SpecTheorem`s (sorted by priority), try to build a backward rule
from the first matching spec.

The backward rule is an auxiliary lemma with excess state arguments made explicit:
for `l = σ1 → ... → σn → Prop`, it turns `pre ⊑ wp x post epost` into
`∀ s1 ... sn, pre s1 ... sn → wp x post epost s1 ... sn`.
-/
def mkBackwardRuleFromSpecs (specThms : Array SpecTheorem)
    (e l instWP : Expr) (excessArgs : Array Expr)
    : MetaM (Option (SpecTheorem × BackwardRule)) := SymM.run do
  for specThm in specThms do
    if let some rule ← withNewMCtxDepth
        (tryMkBackwardRuleFromSpec specThm e l instWP excessArgs) then
      return (specThm, rule)
  return none

/-! ## VCGen monad and caching -/

structure VCGen.Context where
  specThms : SpecTheorems
  -- TODO: entailsConsIntroRule : BackwardRule

structure VCGen.State where
  /-- Cache mapping spec theorem names × WPMonad instance × excess arg count
      to their backward rule. Avoids rebuilding the same aux lemma repeatedly. -/
  specBackwardRuleCache : Std.HashMap (Array Name × Expr × Nat) (SpecTheorem × BackwardRule) := {}
  /-- Cache mapping split rule name × WPMonad instance × excess arg count
      to their backward rule. -/
  splitBackwardRuleCache : Std.HashMap (Name × Expr × Nat) BackwardRule := {}
  /-- Cache mapping logic connective × operand types × excess arg count
      to their backward rule. -/
  logicBackwardRuleCache : Std.HashMap (Name × Array Expr × Nat) BackwardRule := {}
  /-- Holes of type `Invariant` generated so far. -/
  invariants : Array MVarId := #[]
  /-- Verification conditions generated so far. -/
  vcs : Array MVarId := #[]

abbrev VCGenM := ReaderT VCGen.Context (StateRefT VCGen.State SymM)

namespace VCGen

def SpecTheorem.global? (specThm : SpecTheorem) : Option Name :=
  match specThm.proof with | .global decl => some decl | _ => none

/-- Cached version of `mkBackwardRuleFromSpecs`. The cache key is
    `(spec decl names, instWP, excessArgs.size)`. Falls back to the uncached
    version when any spec theorem is not a global declaration. -/
def mkBackwardRuleFromSpecsCached (specThms : Array SpecTheorem)
    (e l instWP : Expr) (excessArgs : Array Expr)
    : OptionT VCGenM (SpecTheorem × BackwardRule) := do
    let decls := specThms.filterMap SpecTheorem.global?
    let s := (← get).specBackwardRuleCache
    match s[(decls, instWP, excessArgs.size)]? with
    | some (specThm, rule) => return (specThm, rule)
    | none =>
      let some rule ← mkBackwardRuleFromSpecs specThms e l instWP excessArgs
        | failure
      let key := (decls, instWP, excessArgs.size)
      modify ({ · with specBackwardRuleCache := s.insert key rule })
      return rule

/-- Cached wrapper for `mkBackwardRuleForIte`. -/
def mkBackwardRuleForIteCached
    (wpHead m l errTy monadInst instWP : Expr)
    (excessArgs : Array Expr) : VCGenM BackwardRule := do
  let s := (← get).splitBackwardRuleCache
  match s[(``ite, instWP, excessArgs.size)]? with
  | some rule => return rule
  | none =>
    let rule ← mkBackwardRuleForIte wpHead m l errTy monadInst instWP excessArgs
    let key := (``ite, instWP, excessArgs.size)
    modify ({ · with splitBackwardRuleCache := s.insert key rule })
    return rule

/-- Cached wrapper for `LogicOp.mkBackwardRuleForLogic`.
    The cache key is `(logic connective, operand types, excessArgs.size)`. -/
def mkBackwardRuleForLogicCached
    (lop : LogicOp) (as excessArgs : Array Expr) : VCGenM BackwardRule := do
  let s := (← get).logicBackwardRuleCache
  let asTypes ← (as.mapM Sym.inferType : SymM (Array Expr))
  let key := (lop.toApplyLemma, asTypes, excessArgs.size)
  match s[key]? with
  | some rule => return rule
  | none =>
    let rule ← lop.mkBackwardRuleForLogic as excessArgs
    modify ({ · with logicBackwardRuleCache := s.insert key rule })
    return rule

inductive SolveResult where
  /-- The target was neither a WP goal nor a supported lattice goal. -/
  | noProgramOrLatticeFoundInTarget (T : Expr)
  /-- Don't know how to handle `e` in `wp e post epost s₁ ... sₙ`. -/
  | noStrategyForProgram (e : Expr)
  /--
  Did not find a spec for the `e` in `wp e post epost s₁ ... sₙ`.
  Candidates were `thms`, but none of them matched the monad.
  -/
  | noSpecFoundForProgram (e : Expr) (monad : Expr) (thms : Array SpecTheorem)
  /-- Successfully discharged the goal. These are the subgoals. -/
  | goals (subgoals : List MVarId)

/-- High-level classifier for goals handled by `solve`. -/
inductive GoalKind where
  /-- Goal is a WP application. We keep the full `withApp` decomposition. -/
  | WP (head : Expr) (args : Array Expr)
  /-- Goal is a lattice connective application (`meet`/`himp`) with optional excess args. -/
  | Lattice (lop : LogicOp) (as : Array Expr) (excessArgs : Array Expr)
  /-- Goal is neither a recognized WP nor a recognized lattice connective. -/
  | Unknown

/-- Classify a goal target as WP, logic-lattice connective, or unknown. -/
def classifyGoalKind (target : Expr) : VCGenM GoalKind := do
  target.withApp fun head args => do
    match_expr head with
    | wp => return .WP head args
    | meet =>
      let excessArgs := args.drop 4
      let as := args.extract 2 4
      return .Lattice .And as excessArgs
    | himp =>
      let excessArgs := args.drop 4
      let as := args.extract 2 4
      return .Lattice .Imp as excessArgs
    | _ => return .Unknown

def solve (goal : MVarId) : VCGenM SolveResult := goal.withContext do
  let target ← goal.getType
  let kind ← classifyGoalKind target
  match kind with
  | .Unknown =>
      return .noProgramOrLatticeFoundInTarget target
  | .Lattice lop as excessArgs => do
      trace[Loom.Tactic.vcgen] "Applying logic rule for {target}. Excess args: {excessArgs}"
      let rule ← mkBackwardRuleForLogicCached lop as excessArgs
      let .goals goals ← rule.apply goal
        | throwError "Failed to apply logic rule at {indentExpr target}"
      let mut out := #[]
      for g in goals do
        out := out ++ (← lop.postProcessGoal g).toArray
      return .goals out.toList
  | .WP head args => do
      -- Goal should be: @WPMonad.wp m l errTy monadInst instWP α e post epost s₁ ... sₙ
      -- WPMonad.wp has 9 base args; anything beyond that are excess state args
      let_expr wp m l errTy monadInst instWP α e post epost :=
        mkAppN head (args.extract 0 (min args.size 9))
        | return .noProgramOrLatticeFoundInTarget target
      let excessArgs := args.extract 9 args.size
      -- Non-dependent let-expressions: use Sym.Simp.simpLet to preserve maximal sharing
      -- TODO: is it the best way?
      let f := e.getAppFn
      if let .letE _x _ty val body _nonDep := f then
        let body' ← Sym.instantiateRevBetaS body #[val]
        let e' ← mkAppRevS body' e.getAppRevArgs
        let wp ← mkAppS₉ head m l errTy monadInst instWP α e' post epost
        let target ← mkAppNS wp excessArgs
        let goal ← goal.replaceTargetDefEq target
        return .goals [goal]

      -- Apply registered specifications
      let f := e.getAppFn
      if f.isConstOf ``ite || f.isAppOf ``ite then
        let rule ← mkBackwardRuleForIteCached head m l errTy monadInst instWP excessArgs
        trace[Loom.Tactic.vcgen] "Applying split rule for {e}. Excess args: {excessArgs}"
        let .goals goals ← rule.apply goal
          | throwError "Failed to apply split rule for {indentExpr e}"
        return .goals goals
      if f.isConst || f.isFVar then
        trace[Loom.Tactic.vcgen] "Applying a spec for {e}. Excess args: {excessArgs}"
        let thms ← (← read).specThms.findSpecs e
        trace[Loom.Tactic.vcgen] "Candidates for {e}: {thms.map (·.proof)}"
        let some (thm, rule) ← (mkBackwardRuleFromSpecsCached thms e l instWP excessArgs).run
          | return .noSpecFoundForProgram e m thms
        trace[Loom.Tactic.vcgen] "Applying rule {rule.pattern.pattern} at {target}"
        let .goals goals ← rule.apply goal
          | throwError "Failed to apply rule {thm.proof} for {indentExpr e}"
        return .goals goals
      return .noStrategyForProgram e

/--
Called when decomposing the goal further did not succeed; in this case we emit a VC for the goal.
-/
meta def emitVC (goal : MVarId) : VCGenM Unit := do
  let ty ← goal.getType
  goal.setKind .syntheticOpaque
  if ty.isAppOf ``Std.Do.Invariant then
    modify fun s => { s with invariants := s.invariants.push goal }
  else
    modify fun s => { s with vcs := s.vcs.push goal }

/-- Unfold `⦃P⦄ x ⦃Q⦄` into `P ⊢ₛ wp⟦x⟧ Q`. -/
meta def unfoldTriple (goal : MVarId) : OptionT SymM MVarId := goal.withContext do
  let type ← goal.getType
  unless type.isAppOf ``Triple do return goal
  let simpTripleMethod <- mkMethods #[``Triple.iff]
  let (res, _) ← Simp.SimpM.run (simpGoal (methods := simpTripleMethod) goal)
  match res with
  | .goal goal => return goal
  | .closed => failure
  | .noProgress => return goal

def introsWP (goal : MVarId) : SymM MVarId := do
  let mut goal := goal
  if (← goal.getType).isForall then
    let IntrosResult.goal _ goal' ← Sym.intros goal | failure
    goal := goal'
  return goal

meta def work (goal : MVarId) : VCGenM Unit := do
  let goal ← preprocessMVar goal
  let some goal ← unfoldTriple goal |>.run | return ()
  let mut worklist := Std.Queue.empty.enqueue goal
  repeat do
    let some (goal, worklist') := worklist.dequeue? | break
    worklist := worklist'
    let res ← solve =<< introsWP goal
    match res with
    | .noProgramOrLatticeFoundInTarget .. =>
      emitVC goal
    | .noSpecFoundForProgram prog _ #[] =>
      throwError "No spec found for program {prog}."
    | .noSpecFoundForProgram prog monad thms =>
      throwError "No spec matching the monad {monad} found for program {prog}. Candidates were {thms.map (·.proof)}."
    | .noStrategyForProgram prog =>
      throwError "Did not know how to decompose weakest precondition for {prog}"
    | .goals subgoals =>
      worklist := worklist.enqueueAll subgoals

public structure Result where
  invariants : Array MVarId
  vcs : Array MVarId

/--
Generate verification conditions for a goal of the form `Triple pre e s₁ ... sₙ` by repeatedly
decomposing `e` using registered `@[spec]` theorems.
Return the VCs and invariant goals.
-/
public meta partial def main (goal : MVarId) (ctx : Context) : SymM Result := do
  let ((), state) ← StateRefT'.run (ReaderT.run (work goal) ctx) {}
  for h : idx in [:state.invariants.size] do
    let mv := state.invariants[idx]
    mv.setTag (Name.mkSimple ("inv" ++ toString (idx + 1)))
  for h : idx in [:state.vcs.size] do
    let mv := state.vcs[idx]
    mv.setTag (Name.mkSimple ("vc" ++ toString (idx + 1)) ++ (← mv.getTag).eraseMacroScopes)
  return { invariants := state.invariants, vcs := state.vcs }


syntax (name := mvcgen') "mvcgen'"
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "] ")? : tactic

@[tactic mvcgen']
public meta def elabMVCGen' : Tactic := fun _stx => withMainContext do
  let ctx ← getSpecTheorems
  let goal ← getMainGoal
  let { invariants, vcs } ← SymM.run <| VCGen.main goal ⟨ctx⟩
  replaceMainGoal (invariants ++ vcs).toList


end VCGen

section Test

/-- Test helper: create a SpecTheorem from a declaration and run tryMkBackwardRuleFromSpec
    with the given monad type expressions. Returns the type of the auxiliary lemma. -/
def testBackwardRule (declName : Name) (e l instWP : Expr)
    (excessArgs : Array Expr) : MetaM Expr := do
  let specThm ← mkSpecTheoremFromConst declName
  let rule ← SymM.run do
    tryMkBackwardRuleFromSpec specThm e l instWP excessArgs
  match rule with
  | some br => inferType br.expr
  | none => throwError "tryMkBackwardRuleFromSpec returned none for {declName}"

/-- Instantiate a spec theorem and extract the program term from `pre ⊑ wp prog post epost`. -/
def mkProgramFromSpec (declName : Name) : MetaM Expr := do
  let specThm ← mkSpecTheoremFromConst declName
  let (_xs, _bs, _specProof, specType) ← specThm.proof.instantiate
  let_expr PartialOrder.rel _ _ _ rhs := specType
    | throwError "target not a partial order ⊑ application {specType}"
  let_expr wp _ _ _ _ _ _ prog _ _ := rhs
    | throwError "target not a wp application {rhs}"
  return prog

/-- Test helper: run `mkSpecBackwardProof` directly and return the proof type plus source data. -/
def testSpecBackwardProofType (declName : Name)
    (excessArgTypes : Array Expr) : MetaM (Expr × Expr × Expr) := do
  let specThm ← mkSpecTheoremFromConst declName
  let (_xs, _bs, specProof, specType) ← specThm.proof.instantiate
  let_expr PartialOrder.rel _ _ pre rhs := specType
    | throwError "target not a partial order ⊑ application {specType}"
  let excessArgNamesTypes := excessArgTypes.map fun ty => (`s, ty)
  let spec ← withLocalDeclsDND excessArgNamesTypes fun ss => do
    let spec ← SymM.run <| mkSpecBackwardProof pre rhs specProof ss excessArgTypes
    mkLambdaFVars ss spec
  let ty ← instantiateMVars (← inferType spec)
  return (ty, pre, rhs)

private def assertExprDefEq (got expected : Expr) (ctx : String) : MetaM Unit := do
  unless (← isDefEqGuarded got expected) do
    throwError "{ctx}\nexpected:{indentExpr expected}\ngot:{indentExpr got}"

private def assertRelPremise (premTy expectedLhs : Expr) (ctx : String) : MetaM Expr := do
  let_expr PartialOrder.rel _ _ lhs rhs := premTy
    | throwError "{ctx}\nexpected relation premise, got:{indentExpr premTy}"
  assertExprDefEq lhs expectedLhs s!"{ctx}\nrelation lhs mismatch"
  unless rhs.consumeMData.isMVar do
    throwError "{ctx}\nexpected relation rhs to be a top-level metavariable, got:{indentExpr rhs}"
  return rhs

private def assertPostPremise
    (premTy postSpec : Expr) (excessArgTypes : Array Expr) (ctx : String) : MetaM Expr := do
  forallBoundedTelescope premTy (some (1 + excessArgTypes.size)) fun xs body => do
    unless xs.size == 1 + excessArgTypes.size do
      throwError "{ctx}\nexpected {1 + excessArgTypes.size} explicit binders, got {xs.size}"
    let x := xs[0]!
    let ss := xs.extract 1 xs.size
    for h : i in [:excessArgTypes.size] do
      let ty ← inferType ss[i]!
      assertExprDefEq ty excessArgTypes[i]
        s!"{ctx}\nexcess binder {i} type mismatch"
    let some (lhs, rhs) := body.arrow?
      | throwError "{ctx}\nexpected implication premise, got:{indentExpr body}"
    assertExprDefEq lhs (mkAppN (mkApp postSpec x) ss) s!"{ctx}\npost premise lhs mismatch"
    let rhsHead := rhs.getAppFn
    let rhsArgs := rhs.getAppArgs
    unless rhsHead.consumeMData.isMVar do
      throwError "{ctx}\nexpected post premise rhs head to be a top-level metavariable, got:{indentExpr rhs}"
    let expectedSuffixSize := ss.size + 1
    unless rhsArgs.size >= expectedSuffixSize do
      throwError "{ctx}\nexpected at least {expectedSuffixSize} rhs arguments, got {rhsArgs.size}"
    let suffixStart := rhsArgs.size - expectedSuffixSize
    assertExprDefEq rhsArgs[suffixStart]! x s!"{ctx}\nresult argument mismatch"
    for h : i in [:ss.size] do
      assertExprDefEq rhsArgs[suffixStart + i + 1]!
        ss[i]
        s!"{ctx}\nexcess argument {i} mismatch"
    return mkAppN rhsHead (rhsArgs.extract 0 suffixStart)

/-- Test helper: run `mkBackwardRuleForIte` with the given monad/lattice expressions.
    Returns the type of the generated auxiliary lemma. -/
def testIteBackwardRule
    (wpHead m l errTy monadInst instWP : Expr)
    (excessArgs : Array Expr) : MetaM Expr := do
  let rule ← SymM.run do
    mkBackwardRuleForIte wpHead m l errTy monadInst instWP excessArgs
  inferType rule.expr

/-- Test helper: run `LogicOp.mkBackwardRuleForLogic` and return the generated rule type. -/
def testLogicBackwardRule
    (lop : LogicOp)
    (as excessArgs : Array Expr) : MetaM Expr := do
  let rule ← SymM.run do lop.mkBackwardRuleForLogic as excessArgs
  inferType rule.expr

-- Test 1: Id monad, l = Prop, n = 0 excess args
-- wp_bind for Id: pre → wp (x >>= f) post ()
#eval! show MetaM Unit from do
  let m := mkConst ``Id [.zero]
  let l := mkSort 0
  let errTy := mkConst ``EPost.nil --[.zero]
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero, .zero]) #[m, l, errTy, monadM])
  let prog ← mkProgramFromSpec ``WPMonad.wp_bind
  let ty ← testBackwardRule ``WPMonad.wp_bind prog l instWP #[]
  logInfo m!"Test 1 (Id, n=0): {ty}"

-- Test 2: StateM Nat, l = Nat → Prop, n = 1 excess arg
-- wp_bind for StateM Nat: ∀ s, pre s → wp (x >>= f) post () s
#eval! show MetaM Unit from do
  let nat := mkConst ``Nat
  let m ← mkAppM ``StateM #[nat]
  let l ← mkArrow nat (mkSort 0)
  let errTy := mkConst ``EPost.nil --[.zero]
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero, .zero]) #[m, l, errTy, monadM])
  let prog ← mkProgramFromSpec ``WPMonad.wp_bind
  withLocalDeclD `s nat fun s => do
    let ty ← testBackwardRule ``WPMonad.wp_bind prog l instWP #[s]
    logInfo m!"Test 2 (StateM Nat, n=1): {ty}"

-- Test 3: get for StateM Nat, n = 1 excess arg
-- Spec.get_StateT': ∀ s, (fun s => post s s) s → wp get post epost s
@[lspec high] theorem spec_get_StateT {m : Type u → Type v} {l e : Type u}
    [Monad m] [WPMonad m l e]
    {σ : Type u} (post : σ → σ → l) (epost : e) :
    Triple (fun s => post s s) (MonadStateOf.get : StateT σ m σ) post epost := by
  exact ⟨WP.get_StateT_wp post epost⟩

#eval! show MetaM Unit from do
  let nat := mkConst ``Nat
  let m ← mkAppM ``StateM #[nat]
  let l ← mkArrow nat (mkSort 0)
  let errTy := mkConst ``EPost.nil --[.zero]
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero, .zero]) #[m, l, errTy, monadM])
  let prog ← mkProgramFromSpec ``spec_get_StateT
  withLocalDeclD `s nat fun s => do
    let ty ← testBackwardRule ``spec_get_StateT prog l instWP #[s]
    logInfo m!"Test 3 (get StateM Nat, n=1): {ty}"

@[local lspec high]
theorem spec_set_concretePost_test (epost : EPost.nil) :
    wp (set (m := StateM Nat) 7) (fun _ _ => True) epost ⊑
      wp (set (m := StateM Nat) 7) (fun _ _ => True) epost := by
  exact PartialOrder.rel_refl

#eval! show MetaM Unit from do
  let nat := mkConst ``Nat
  let (ty, pre, rhs) ← testSpecBackwardProofType ``spec_set_concretePost_test #[nat]
  let_expr wp _ _ _ _ _ _ _ postSpec epostSpec := rhs
    | throwError "Test A: target not a wp application {rhs}"
  let ty ← whnfD ty
  let .forallE _ sTy body _ := ty
    | throwError "Test A: expected an excess-arg binder, got {ty}"
  withLocalDeclD `s sTy fun s => do
    let body := body.instantiate1 s
    let preApplied := mkAppN pre #[s]
    let some (hpostTy, body) := body.arrow?
      | throwError "Test A: expected post premise"
    let some (hpreTy, body) := body.arrow?
      | throwError "Test A: expected pre premise"
    let postTarget ← assertPostPremise hpostTy postSpec #[nat] "Test A"
    assertExprDefEq hpreTy preApplied "Test A: pre premise mismatch"
    let expectedWp ← mkWpWithPostEPost rhs postTarget epostSpec
    let expectedBody := mkAppN expectedWp #[s]
    assertExprDefEq body expectedBody "Test A: conclusion mismatch"

@[local lspec high]
theorem spec_throw_concreteEPost_test (post : PUnit → Prop) :
    wp (MonadExceptOf.throw "boom" : Except String PUnit) post epost⟨fun _ => True⟩ ⊑
      wp (MonadExceptOf.throw "boom" : Except String PUnit) post epost⟨fun _ => True⟩ := by
  exact PartialOrder.rel_refl

#eval! show MetaM Unit from do
  let (ty, pre, rhs) ← testSpecBackwardProofType ``spec_throw_concreteEPost_test #[]
  let_expr wp _ _ _ _ _ _ _ postSpec epostSpec := rhs
    | throwError "Test B: target not a wp application {rhs}"
  let preApplied := mkAppN pre #[]
  let some (hepostTy, body) := ty.arrow?
    | throwError "Test B: expected epost premise"
  let some (hpreTy, body) := body.arrow?
    | throwError "Test B: expected pre premise"
  let epostTarget ← assertRelPremise hepostTy epostSpec "Test B"
  assertExprDefEq hpreTy preApplied "Test B: pre premise mismatch"
  let expectedWp ← mkWpWithPostEPost rhs postSpec epostTarget
  let expectedBody := mkAppN expectedWp #[]
  assertExprDefEq body expectedBody "Test B: conclusion mismatch"

@[local lspec high]
theorem spec_throw_concretePostEPost_test :
    wp (MonadExceptOf.throw "boom" : Except String PUnit) (fun _ => True) epost⟨fun _ => True⟩ ⊑
      wp (MonadExceptOf.throw "boom" : Except String PUnit) (fun _ => True) epost⟨fun _ => True⟩ := by
  exact PartialOrder.rel_refl

#eval! show MetaM Unit from do
  let (ty, pre, rhs) ← testSpecBackwardProofType ``spec_throw_concretePostEPost_test #[]
  let_expr wp _ _ _ _ _ _ _ postSpec epostSpec := rhs
    | throwError "Test C: target not a wp application {rhs}"
  let preApplied := mkAppN pre #[]
  let some (hpostTy, body) := ty.arrow?
    | throwError "Test C: expected post premise"
  let some (hepostTy, body) := body.arrow?
    | throwError "Test C: expected epost premise"
  let some (hpreTy, body) := body.arrow?
    | throwError "Test C: expected pre premise"
  let postTarget ← assertPostPremise hpostTy postSpec #[] "Test C"
  let epostTarget ← assertRelPremise hepostTy epostSpec "Test C"
  assertExprDefEq hpreTy preApplied "Test C: pre premise mismatch"
  let expectedWp ← mkWpWithPostEPost rhs postTarget epostTarget
  let expectedBody := mkAppN expectedWp #[]
  assertExprDefEq body expectedBody "Test C: conclusion mismatch"

-- Test 4: ite for StateM Nat, n = 1 excess arg
-- mkBackwardRuleForIte:
--   ∀ s, (c → wp t post epost s) → (¬c → wp e post epost s) → wp (ite c t e) post epost s
#eval! show MetaM Unit from do
  let nat := mkConst ``Nat
  let m ← mkAppM ``StateM #[nat]
  let l ← mkArrow nat (mkSort 0)
  let errTy := mkConst ``EPost.nil --[.zero]
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance
    (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero, .zero]) #[m, l, errTy, monadM])
  let wpHead := mkConst ``wp [.zero, .zero, .zero, .zero]
  withLocalDeclD `s nat fun s => do
    let ty ← testIteBackwardRule wpHead m l errTy monadM instWP #[s]
    logInfo m!"Test 4 (ite StateM Nat, n=1): {ty}"

-- Test 5: ite for Id, n = 0 excess args
#eval! show MetaM Unit from do
  let m := mkConst ``Id [.zero]
  let l := mkSort 0
  let errTy := mkConst ``EPost.nil --[.zero]
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance
    (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero, .zero]) #[m, l, errTy, monadM])
  let wpHead := mkConst ``wp [.zero, .zero, .zero, .zero]
  let ty ← testIteBackwardRule wpHead m l errTy monadM instWP #[]
  logInfo m!"Test 5 (ite Id, n=0): {ty}"

-- Test 8: logic And on Prop, n = 0 excess args
#eval! show MetaM Unit from do
  let l := mkSort 0
  withLocalDeclD `a l fun a => do
    withLocalDeclD `b l fun b => do
      let ty ← testLogicBackwardRule .And #[a, b] #[]
      logInfo m!"Test 8 (logic And Prop, n=0): {ty}"

-- Test 9: logic And on Nat → Prop, n = 1 excess arg
#eval! show MetaM Unit from do
  let nat := mkConst ``Nat
  let l ← mkArrow nat (mkSort 0)
  withLocalDeclD `a l fun a => do
    withLocalDeclD `b l fun b => do
      withLocalDeclD `s nat fun s => do
        let ty ← testLogicBackwardRule .And #[a, b] #[s]
        logInfo m!"Test 9 (logic And Nat→Prop, n=1): {ty}"

-- Test 10: logic Imp on Nat → Prop, n = 1 excess arg
#eval! show MetaM Unit from do
  let nat := mkConst ``Nat
  let l ← mkArrow nat (mkSort 0)
  withLocalDeclD `a l fun a => do
    withLocalDeclD `b l fun b => do
      withLocalDeclD `s nat fun s => do
        let ty ← testLogicBackwardRule .Imp #[a, b] #[s]
        logInfo m!"Test 10 (logic Imp Nat→Prop, n=1): {ty}"

-- -- Test 11/12 (Forall) are temporarily disabled while LogicOp.Forall is commented out.

namespace MTest
section
abbrev M := ExceptT String <| ReaderT String <| ExceptT Nat <| StateT Nat <| ExceptT Unit <| StateM Unit

@[local lspec high]
theorem Spec.M_getThe_Nat :
  Triple (fun s₁ s₂ => post s₂ s₁ s₂) (get (σ := Nat) (m := M)) post epost := by
  sorry

#eval! show MetaM Unit from do
  let string := mkConst ``String
  let nat := mkConst ``Nat
  let unit := mkConst ``Unit
  let m := mkConst ``M
  let l ← mkArrow string (← mkArrow nat (← mkArrow unit (mkSort 0)))
  let e1 ← mkArrow string (← mkArrow string (← mkArrow nat (← mkArrow unit (mkSort 0))))
  let e2 ← mkArrow nat (← mkArrow nat (← mkArrow unit (mkSort 0)))
  let e3 ← mkArrow unit (← mkArrow unit (mkSort 0))
  let enil := mkConst ``EPost.nil --[.zero]
  let e34 ← mkAppM ``EPost.cons #[e3, enil]
  let e234 ← mkAppM ``EPost.cons #[e2, e34]
  let errTy ← mkAppM ``EPost.cons #[e1, e234]
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero, .zero]) #[m, l, errTy, monadM])
  let prog ← mkProgramFromSpec ``Spec.M_getThe_Nat
  withLocalDeclD `s₁ string fun s₁ => do
    withLocalDeclD `s₂ nat fun s₂ => do
      withLocalDeclD `s₃ unit fun s₃ => do
        let ty ← testBackwardRule ``Spec.M_getThe_Nat prog l instWP #[s₁, s₂, s₃]
        logInfo m!"Test 6 (Spec.M_getThe_Nat): {ty}"

-- Test 7: ite for deep M, n = 3 excess args
#eval! show MetaM Unit from do
  let string := mkConst ``String
  let nat := mkConst ``Nat
  let unit := mkConst ``Unit
  let m := mkConst ``M
  let l ← mkArrow string (← mkArrow nat (← mkArrow unit (mkSort 0)))
  let e1 ← mkArrow string (← mkArrow string (← mkArrow nat (← mkArrow unit (mkSort 0))))
  let e2 ← mkArrow nat (← mkArrow nat (← mkArrow unit (mkSort 0)))
  let e3 ← mkArrow unit (← mkArrow unit (mkSort 0))
  let enil := mkConst ``EPost.nil --[.zero]
  let e34 ← mkAppM ``EPost.cons #[e3, enil]
  let e234 ← mkAppM ``EPost.cons #[e2, e34]
  let errTy ← mkAppM ``EPost.cons #[e1, e234]
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance
    (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero, .zero]) #[m, l, errTy, monadM])
  let wpHead := mkConst ``wp [.zero, .zero, .zero, .zero]
  withLocalDeclD `s₁ string fun s₁ => do
    withLocalDeclD `s₂ nat fun s₂ => do
      withLocalDeclD `s₃ unit fun s₃ => do
        let ty ← testIteBackwardRule wpHead m l errTy monadM instWP #[s₁, s₂, s₃]
        logInfo m!"Test 7 (ite M, n=3): {ty}"


-- @[lspec] theorem spec_set_StateT {m : Type u → Type v} {l e : Type u}
--     [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e]
--     {σ : Type u} (x : σ) (post : PUnit → σ → l) (epost : e) :
--     (fun _ => post ⟨⟩ x) ⊑ wp (MonadStateOf.set x : StateT σ m PUnit) post epost := by
--   exact WP.set_StateT_wp x post epost

end
end MTest
end Test

end Loom
