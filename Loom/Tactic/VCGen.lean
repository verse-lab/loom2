import Lean
import Loom.Tactic.Attr
import Loom.Triple.Basic
import Loom.Triple.SpecLemmas
import Loom.WP.SimpLemmas
import Lean.Meta

open Lean Parser Meta Elab Tactic Sym Loom Lean.Order
open Loom.Tactic.SpecAttr

namespace Loom

def entails [CompleteLattice l] (P Q : l) : Prop :=
  P ⊑ Q

macro:25 p:term:26 " ⊢ " q:term:25 : term => `(binrel% entails $p $q)

def entails.rfl [CompleteLattice l] {P : l} : P ⊢ P :=
  PartialOrder.rel_refl

def entails.trans [CompleteLattice l] {P Q R : l} (hPQ : P ⊢ Q) (hQR : Q ⊢ R) : P ⊢ R :=
  PartialOrder.rel_trans hPQ hQR

def entails.funext [CompleteLattice l] {P Q : α → l} (h : ∀ a, P a ⊢ Q a) : P ⊢ Q :=
  h

def Triple.of_entails_wp [Monad m] [CompleteLattice l] [WPMonad m l e]
    {pre : l} {x : m α} {post : α → l} {epost : e} (h : pre ⊢ wp x post epost) :
    Triple pre x post epost :=
  Triple.iff.mpr h

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


/--
TODO:
  - Transform Triple to ⊑ at @[lspec] level
  - add abstraction over `post` and `epost`

Try to build a backward rule from a single spec theorem in `⊑` form.

Given a spec `pre ⊑ wp prog post epost` where the lattice type is
`l = σ1 → ... → σn → Prop`, produces an auxiliary lemma of the form
`∀ s1 ... sn, pre s1 ... sn → wp prog post epost s1 ... sn`.

This conversion is necessary because `PartialOrder.rel` is a projection (not unfolded
by `unfoldReducible`), so `mkPatternFromType` cannot structurally see the `→`. We
explicitly construct the `→` type via `mkExpectedTypeHint`.

- `l`: the goal's lattice type (e.g. `Nat → Prop`)
- `instWP`: the `WPMonad` instance for the goal monad; matching against the spec's
  instance transitively unifies `m`, `e`, `cl`, and `monadInst`
- `excessArgs`: free variables representing state args from `l = σ1 → ... → σn → Prop`;
  fresh metavariables are created for these so that `abstractMVars` can abstract them
  alongside the spec's universally quantified parameters
-/
def tryMkBackwardRuleFromSpec (specThm : SpecTheorem)
  (instWP : Expr) (excessArgs : Array Expr) : OptionT SymM BackwardRule := do
  -- Instantiate the spec theorem, creating metavars for all universally quantified params
  let (_xs, _bs, specProof, specType) ← specThm.proof.instantiate
  let_expr PartialOrder.rel _l _cl' pre rhs := specType
    | throwError "target not a partial order ⊑ application {specType}"
  let_expr wp _m' _ _e' _monadInst' _cl' instWP' _α _prog _post _epost := rhs
    | throwError "target not a wp application {rhs}"
  -- Unifying instWP transitively assigns m, e, cl, monadInst via type-level unification
  guard <| ← isDefEqGuarded instWP instWP'
  -- Create fresh metavars for excess state args (abstractMVars will bind them as ∀)
  let ss ← excessArgs.mapM fun arg => do
    mkFreshExprMVar (userName := `s) <| ← Sym.inferType arg
  -- Build: pre s1 ... sn → wp prog post epost s1 ... sn
  -- Using mkExpectedTypeHint because PartialOrder.rel is a projection that
  -- unfoldReducible/mkPatternFromType cannot see through structurally
  let proofType ← mkArrow (mkAppN pre ss) (mkAppN rhs ss)
  let spec ← mkExpectedTypeHint (mkAppN specProof ss) proofType
  -- Abstract all remaining metavars (spec params + excess args) into an aux lemma
  let res ← abstractMVars spec
  let type ← preprocessExpr (← Sym.inferType res.expr)
  let spec ← Meta.mkAuxLemma res.paramNames.toList type res.expr
  logInfo m!"type of spec theorem: {type}"
  mkBackwardRuleFromDecl spec

meta def mkBackwardRuleFromSpecs (specThms : Array SpecTheorem) (l instCL instWP : Expr) (excessArgs : Array Expr) : SymM (Option (SpecTheorem × BackwardRule)) := do
  let preprocessExpr : Expr → SymM Expr := shareCommon <=< liftMetaM ∘ unfoldReducible
  for specThm in specThms do
    -- Create a backward rule for the spec we look up in the database.
    -- In order for the backward rule to apply, we need to instantiate both `m` and `ps` with the ones
    -- given by the use site.
    let (xs, _bs, specProof, specType) ← specThm.proof.instantiate
    let_expr PartialOrder.rel _l _instCL pre wpApp := specType
      | throwError "target not a partial order ⊑ application {specType}"
    let_expr wpConst@wp _m' _l' _e' _instMonad _cl' instWP' _α _prog post epost := wpApp
      | throwError "target not a wp application {wpApp}"
    -- Unifying instWP transitively assigns m, e, l, instMonad, instCL
    guard <| ← isDefEqGuarded instWP instWP'
    -- Create fresh metavars for excess state args (abstractMVars will bind them as ∀)
    let ss ← excessArgs.mapM fun arg => do
      mkFreshExprMVar (userName := `s) <| ← Sym.inferType arg

    -- We must ensure that `pre`, `post` and `epost` are pattern variables
    -- so that the spec matches for every potential situation.
    -- We do so by introducing VCs accordingly.
    let needPreVC := !excessArgs.isEmpty || !xs.contains pre
    let needPostVC := !xs.contains post || !xs.contains epost
    let us := wpConst.constLevels!
    let u := us[0]!
    let v := us[1]!
    let w := us[2]!
    let wpApp ← instantiateMVars wpApp
    let preSs := mkAppN pre ss  -- pre s₁ ... sₙ

    let typeP ← preprocessExpr l
      -- Note that this is the type of `pre s₁ ... sₙ`,
      -- which is `Assertion ps'`, but we don't know `ps'`
    let typeQ ← preprocessExpr (mkApp2 (mkConst ``PostCond [u]) α ps)

    let mut declInfos := #[]
    if needPreVC then
      let nmP' ← mkFreshUserName `P
      let nmHPre ← mkFreshUserName `hpre
      let entailment P' := mkApp3 (mkConst ``entails [u]) l instCL P' Pss
      declInfos := #[(nmP', .default, fun _ => pure l),
                     (nmHPre, .default, fun xs => entailment xs[0]!)]
    if needPostVC then
      let nmQ' ← mkFreshUserName `Q
      let nmHPost ← mkFreshUserName `hpost
      let entailment Q' := pure <| mkApp3 (mkConst ``PostCond.entails [u]) ps Q Q'
      declInfos := declInfos ++
                   #[(nmQ', .default, fun _ => pure typeQ),
                     (nmHPost, .default, fun xs => entailment xs[0]!)]
    withLocalDecls declInfos fun ys => liftMetaM ∘ mkLambdaFVars (ss ++ ys) =<< do
      if !needPreVC && !needPostVC && excessArgs.isEmpty then
        -- Still need to unfold the triple in the spec type
        let entailment ← preprocessExpr <| mkApp3 (mkConst ``SPred.entails [u]) σs P wpApplyQ
        let prf ← mkExpectedTypeHint spec entailment
        -- check prf
        return prf
      let mut prf := spec
      let P := Pss  -- P s₁ ... sₙ
      let wpApplyQ := mkAppN wpApplyQ ss  -- wp⟦prog⟧ Q s₁ ... sₙ
      prf := mkAppN prf ss -- Turn `⦃P⦄ prog ⦃Q⦄` into `P s₁ ... sₙ ⊢ₛ wp⟦prog⟧ Q s₁ ... sₙ`
      let mut newP := P
      let mut newQ := Q
      if needPreVC then
        -- prf := hpre.trans prf
        let P' := ys[0]!
        let hpre := ys[1]!
        prf := mkApp6 (mkConst ``SPred.entails.trans [u]) σs P' P wpApplyQ hpre prf
        newP := P'
        -- check prf
      if needPostVC then
        -- prf := prf.trans <| (wp x).mono _ _ hpost
        let wp := mkApp5 (mkConst ``WP.wp f.constLevels!) m ps instWP α prog
        let Q' := ys[ys.size-2]!
        let hpost := ys[ys.size-1]!
        let wpApplyQ' := mkApp4 (mkConst ``PredTrans.apply [u]) ps α wp Q' -- wp⟦prog⟧ Q'
        let wpApplyQ' := mkAppN wpApplyQ' ss -- wp⟦prog⟧ Q' s₁ ... sₙ
        let hmono := mkApp6 (mkConst ``PredTrans.mono [u]) ps α wp Q Q' hpost
        let hmono := mkAppN hmono ss
        prf := mkApp6 (mkConst ``SPred.entails.trans [u]) σs newP wpApplyQ wpApplyQ' prf hmono
        newQ := Q'
        -- check prf
      return prf
    let res ← abstractMVars spec
    let type ← preprocessExpr (← Sym.inferType res.expr)
    trace[Elab.Tactic.Do.vcgen] "Type of new auxiliary spec apply theorem: {type}"
    let spec ← Meta.mkAuxLemma res.paramNames.toList type res.expr
    return some (specThm, ← mkBackwardRuleFromDecl spec)
  return none


/--
Given an array of `SpecTheorem`s (sorted by priority), try to build a backward rule
from the first matching spec.

The backward rule is an auxiliary lemma with excess state arguments made explicit:
for `l = σ1 → ... → σn → Prop`, it turns `pre ⊑ wp x post epost` into
`∀ s1 ... sn, pre s1 ... sn → wp x post epost s1 ... sn`.
-/
def mkBackwardRuleFromSpecs (specThms : Array SpecTheorem)
    (instWP : Expr) (excessArgs : Array Expr)
    : MetaM (Option (SpecTheorem × BackwardRule)) := SymM.run do
  for specThm in specThms do
    if let some rule ← withNewMCtxDepth
        (tryMkBackwardRuleFromSpec specThm instWP excessArgs) then
      return (specThm, rule)
  return none

/-! ## VCGen monad and caching -/

structure VCGen.Context where
  specThms : SpecTheorems
  entailsFunextRule : BackwardRule

structure VCGen.State where
  /-- Cache mapping spec theorem names × WPMonad instance × excess arg count
      to their backward rule. Avoids rebuilding the same aux lemma repeatedly. -/
  specBackwardRuleCache : Std.HashMap (Array Name × Expr × Nat) (SpecTheorem × BackwardRule) := {}
  /-- Holes of type `Invariant` generated so far. -/
  invariants : Array MVarId := #[]
  /-- Verification conditions generated so far. -/
  vcs : Array MVarId := #[]

abbrev VCGenM := ReaderT VCGen.Context (StateRefT VCGen.State SymM)

namespace VCGen

@[inline] def _root_.Std.HashMap.getDM [Monad m] [BEq α] [Hashable α]
    (cache : Std.HashMap α β) (key : α) (fallback : m β) : m (β × Std.HashMap α β) := do
  if let some b := cache.get? key then
    return (b, cache)
  let b ← fallback
  return (b, cache.insert key b)

def SpecTheorem.global? (specThm : SpecTheorem) : Option Name :=
  match specThm.proof with | .global decl => some decl | _ => none

/-- Cached version of `mkBackwardRuleFromSpecs`. The cache key is
    `(spec decl names, instWP, excessArgs.size)`. Falls back to the uncached
    version when any spec theorem is not a global declaration. -/
def mkBackwardRuleFromSpecsCached (specThms : Array SpecTheorem)
    (instWP : Expr) (excessArgs : Array Expr)
    : OptionT VCGenM (SpecTheorem × BackwardRule) := do
    let decls := specThms.filterMap SpecTheorem.global?
    let s := (← get).specBackwardRuleCache
    let key := (decls, instWP, excessArgs.size)
    match s[key]? with
    | some (specThm, rule) => return (specThm, rule)
    | none =>
      let some rule ← mkBackwardRuleFromSpecs specThms instWP excessArgs
        | failure
      modify ({ · with specBackwardRuleCache := s.insert key rule })
      return rule

inductive SolveResult where
  /-- `target` was not of the form `H ⊢ₛ T`. -/
  | noEntailment (target : Expr)
  /-- The `T` was not of the form `wp e post epost s₁ ... sₙ`. -/
  | noProgramFoundInTarget (T : Expr)
  /-- Don't know how to handle `e` in `wp e post epost s₁ ... sₙ`. -/
  | noStrategyForProgram (e : Expr)
  /--
  Did not find a spec for the `e` in `wp e post epost s₁ ... sₙ`.
  Candidates were `thms`, but none of them matched the monad.
  -/
  | noSpecFoundForProgram (e : Expr) (monad : Expr) (thms : Array SpecTheorem)
  /-- Successfully discharged the goal. These are the subgoals. -/
  | goals (subgoals : List MVarId)


def solve (goal : MVarId) : VCGenM SolveResult := goal.withContext do
  let target ← goal.getType
  trace[Elab.Tactic.Do.vcgen] "target: {target}"
  let_expr ent@entails l _instCL H T := target | return .noEntailment target
  -- The goal is of the form `H ⊢ₛ T`. Look for program syntax in `T`.

  if T.isLambda then
    -- This happens after applying the `get` spec. We have `T = (fun s => (wp⟦e⟧ Q, Q.snd).fst s s)`.
    -- Do what `mIntroForall` does, that is, eta-expand. Note that this introduces an
    -- extra state arg `s` to reduce away the lambda.
    let .goals goals ← (← read).entailsFunextRule.apply goal
      | throwError "Applying {.ofConstName ``entails.funext} to {target} failed. It should not."
    return .goals goals

  T.withApp fun head args => do

  if head.isMVar then
    if ← withAssignableSyntheticOpaque <| isDefEq H T then -- TODO: Figure out why `isDefEqS` doesn't work here
      goal.assign (mkApp2 (mkConst ``PartialOrder.rel_refl ent.constLevels!) l H)
      return .goals []

  -- WPMonad.wp has 10 base args; anything beyond that are excess state args
  unless head.isConstOf ``wp do return .noProgramFoundInTarget T
  -- `T` is of the form
  -- `@WPMonad.wp m l err instMonad instCL instWP α prog post epost s₁ ... sₙ`,
  -- where `prog` is the program.
  -- We call `s₁ ... sₙ` the excess state args; the backward rules need to account for these.
  -- Excess state args are introduced by the spec of `get` (see lambda case above).
  let instWP := args[5]!
  let prog := args[7]!
  let excessArgs := args.drop 10
  let f := prog.getAppFn
  withTraceNode `Elab.Tactic.Do.vcgen (msg := fun _ => return m!"Program: {prog}") do

  -- Non-dependent let-expressions: use Sym.Simp.simpLet to preserve maximal sharing
  -- TODO: is it the best way?
  if prog.isLet then
    if let .step prog' .. ← Simp.SimpM.run' (Simp.simpLet prog) then
      let target' ← share <| mkAppN head (args.set! 7 prog')
      return .goals [← goal.replaceTargetDefEq target']
    else return .noStrategyForProgram prog

  -- Hard-code match splitting for `ite` for now.
  -- if f.isAppOf ``ite then
  --   let some info ← Lean.Elab.Tactic.Do.getSplitInfo? e | return .noStrategyForProgram e
  --   let rule ← mkBackwardRuleFromSplitInfoCached info m σs ps instWP excessArgs
  --   let ApplyResult.goals goals ← rule.apply goal
  --     | throwError "Failed to apply split rule for {indentExpr e}"
  --   return .goals goals

  -- Apply registered specifications
  if f.isConst || f.isFVar then
    trace[Elab.Tactic.Do.vcgen] "Applying a spec for {prog}. Excess args: {excessArgs}"
    let thms ← (← read).specThms.findSpecs prog
    trace[Elab.Tactic.Do.vcgen] "Candidates for {prog}: {thms.map (·.proof)}"
    let some (_, rule) ← (mkBackwardRuleFromSpecsCached thms instWP excessArgs).run
      | return .noSpecFoundForProgram prog args[3]! thms
    trace[Elab.Tactic.Do.vcgen] "Applying rule {rule.pattern.pattern} at {target}"
    let .goals goals ← rule.apply goal
      | throwError "Failed to apply rule for {indentExpr prog}"
    return .goals goals

  return .noStrategyForProgram prog

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
  let rule ← mkBackwardRuleFromDecl ``Triple.of_entails_wp
  let .goals [goal] ← rule.apply goal | return goal
  return goal

meta def work (goal : MVarId) : VCGenM Unit := do
  let goal ← preprocessMVar goal
  let some goal ← unfoldTriple goal |>.run | return ()
  let mut worklist := Std.Queue.empty.enqueue goal
  repeat do
    let some (goal, worklist') := worklist.dequeue? | break
    worklist := worklist'
    -- let some goal ← preprocessGoal goal | continue
    let res ← solve goal
    match res with
    | .noEntailment .. | .noProgramFoundInTarget .. =>
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
  let specThms ← getSpecTheorems
  let entailsFunextRule ← mkBackwardRuleFromDecl ``entails.funext
  let goal ← getMainGoal
  let { invariants, vcs } ← SymM.run <| VCGen.main goal {specThms, entailsFunextRule}
  replaceMainGoal (invariants ++ vcs).toList


end VCGen

section Test

/-- Test helper: create a SpecTheorem from a declaration and run tryMkBackwardRuleFromSpec
    with the given monad type expressions. Returns the type of the auxiliary lemma. -/
def testBackwardRule (declName : Name) (instWP : Expr)
    (excessArgs : Array Expr) : MetaM Expr := do
  let specThm ← mkSpecTheoremFromConst declName
  let rule ← SymM.run do
    tryMkBackwardRuleFromSpec specThm instWP excessArgs
  match rule with
  | some br => inferType br.expr
  | none => throwError "tryMkBackwardRuleFromSpec returned none for {declName}"

-- Test 1: Id monad, l = Prop, n = 0 excess args
-- wp_bind for Id: pre → wp (x >>= f) post ()
#eval show MetaM Unit from do
  let m := mkConst ``Id [.zero]
  let l := mkSort 0
  let e := mkConst ``Unit
  let cl ← synthInstance (← mkAppM ``CompleteLattice #[l])
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero]) #[m, l, e, monadM, cl])
  let ty ← testBackwardRule ``WPMonad.wp_bind instWP #[]
  logInfo m!"Test 1 (Id, n=0): {ty}"

-- Test 2: StateM Nat, l = Nat → Prop, n = 1 excess arg
-- wp_bind for StateM Nat: ∀ s, pre s → wp (x >>= f) post () s
#eval show MetaM Unit from do
  let nat := mkConst ``Nat
  let m ← mkAppM ``StateM #[nat]
  let l ← mkArrow nat (mkSort 0)
  let e := mkConst ``Unit
  let cl ← synthInstance (← mkAppM ``CompleteLattice #[l])
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero]) #[m, l, e, monadM, cl])
  withLocalDeclD `s nat fun s => do
    let ty ← testBackwardRule ``WPMonad.wp_bind instWP #[s]
    logInfo m!"Test 2 (StateM Nat, n=1): {ty}"

-- Test 3: get for StateM Nat, n = 1 excess arg
-- Spec.get_StateT': ∀ s, (fun s => post s s) s → wp get post epost s
@[lspec] theorem spec_get_StateT {m : Type u → Type v} {l e : Type u}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e]
    {σ : Type u} (post : σ → σ → l) (epost : e) :
    (fun s => post s s) ⊑ wp (MonadStateOf.get : StateT σ m σ) post epost := by
  rw [WP.get_StateT_wp]

#eval show MetaM Unit from do
  let nat := mkConst ``Nat
  let m ← mkAppM ``StateM #[nat]
  let l ← mkArrow nat (mkSort 0)
  let e := mkConst ``Unit
  let cl ← synthInstance (← mkAppM ``CompleteLattice #[l])
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero]) #[m, l, e, monadM, cl])
  withLocalDeclD `s nat fun s => do
    let ty ← testBackwardRule ``spec_get_StateT instWP #[s]
    logInfo m!"Test 3 (get StateM Nat, n=1): {ty}"

@[lspec] theorem spec_set_StateT {m : Type u → Type v} {l e : Type u}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e]
    {σ : Type u} (x : σ) (post : PUnit → σ → l) (epost : e) :
    (fun _ => post ⟨⟩ x) ⊑ wp (MonadStateOf.set x : StateT σ m PUnit) post epost := by
  rw [WP.set_StateT_wp]

-- Specs for the standalone `get`/`set` functions (which elaborate to MonadState.get/set,
-- a different head constant from MonadStateOf.get/set used above).
@[lspec] theorem spec_get_StateT' {m : Type u → Type v} {l e : Type u}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e]
    {σ : Type u} (post : σ → σ → l) (epost : e) :
    (fun s => post s s) ⊑ wp (get : StateT σ m σ) post epost :=
  spec_get_StateT post epost

@[lspec] theorem spec_set_StateT' {m : Type u → Type v} {l e : Type u}
    [CompleteLattice l] [Monad m] [LawfulMonad m] [WPMonad m l e]
    {σ : Type u} (x : σ) (post : PUnit → σ → l) (epost : e) :
    (fun _ => post ⟨⟩ x) ⊑ wp (set x : StateT σ m PUnit) post epost :=
  spec_set_StateT x post epost

@[lspec] theorem spec_pure {m : Type u → Type v} {l e : Type u}
    [Monad m] [CompleteLattice l] [WPMonad m l e]
    {α : Type u} (a : α) (post : α → l) (epost : e) :
    post a ⊑ wp (pure (f := m) a) post epost := by
  rw [WPMonad.wp_pure]

@[lspec] theorem spec_bind {m : Type u → Type v} {l e : Type u}
    [Monad m] [CompleteLattice l] [WPMonad m l e]
    {α β : Type u} (x : m α) (f : α → m β) (post : β → l) (epost : e) :
    wp x (fun a => wp (f a) post epost) epost ⊑ wp (x >>= f) post epost :=
  WPMonad.wp_bind x f post epost

end Test

end Loom
