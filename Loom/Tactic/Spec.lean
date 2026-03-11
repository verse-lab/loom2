/-
Pattern-based spec theorem lookup and backward rule construction for VCGen'.
Contains the full FindSpec logic plus tryMkBackwardRuleFromSpec.
-/
import Lean
import Loom.Tactic.Attr
import Loom.Tactic.Logic
import Loom.Triple.Basic

namespace Loom.Tactic.Spec

open Lean Meta Loom Lean.Order Sym
open Loom.Tactic.SpecAttr

/-! ## Spec lookup (from FindSpec) -/

/-- Extract the program expression from a spec conclusion (Triple or ⊑ wp form). -/
private def selectProg (type : Expr) : MetaM (Expr × Unit) := do
  let type ← whnfR type
  if type.isAppOfArity ``Triple 10 then
    return (type.getArg! 7, ())
  else if type.isAppOfArity ``PartialOrder.rel 4 then
    let rhs := type.getArg! 3
    let_expr wp _m _l _e _monad _wpInst _α prog _post _epost := rhs
      | throwError "RHS of ⊑ is not a wp application{indentExpr rhs}"
    return (prog, ())
  else
    throwError "expected Triple or ⊑ wp{indentExpr type}"

/-- Create a `Sym.Pattern` for a `SpecTheorem` by extracting the program from the proof type. -/
private def mkSpecPattern (proof : SpecProof) : SymM Sym.Pattern := do
  match proof with
  | .global declName =>
    Prod.fst <$> Sym.mkPatternFromDeclWithKey declName selectProg
  | .local fvarId =>
    let e := mkFVar fvarId
    Prod.fst <$> Sym.mkPatternFromExprWithKey e [] selectProg
  | .stx _ _ proof =>
    Prod.fst <$> Sym.mkPatternFromExprWithKey proof [] selectProg

/--
Migrate a `SpecTheorems` database by computing `Sym.Pattern`s for each spec theorem
and rebuilding the discrimination tree using pattern-derived keys.
-/
def migrateSpecTheoremsDatabase (database : SpecTheorems) : SymM SpecTheorems := do
  let oldSpecs := database.specs.values
  let mut newSpecs : DiscrTree SpecTheorem := DiscrTree.empty
  for spec in oldSpecs do
    if database.erased.contains spec.proof then continue
    try
      let pattern ← mkSpecPattern spec.proof
      let newSpec := { spec with pattern := some pattern }
      newSpecs := Sym.insertPattern newSpecs pattern newSpec
    catch _ =>
      -- Fall back to old keys if pattern creation fails
      newSpecs := newSpecs.insertKeyValue spec.keys spec
  return { database with specs := newSpecs }

/--
Look up spec theorems matching program `e` using pattern-based matching.
Returns `.ok spec` on the first match, or `.error candidates` if no spec matches.
-/
def findSpecs (database : SpecTheorems) (e : Expr) :
    SymM (Except (Array SpecTheorem) SpecTheorem) := do
  let e ← instantiateMVars e
  let e ← shareCommon e
  let candidates := Sym.getMatch database.specs e
  let candidates := candidates.filter (!database.erased.contains ·.proof)
  if h : candidates.size = 1 then return .ok candidates[0]
  let candidates := candidates.insertionSort (·.priority > ·.priority)
  for spec in candidates do
    match spec.pattern with
    | some pattern =>
      let some _res ← pattern.match? e | continue
      return .ok spec
    | none =>
      -- Fallback for specs without patterns (shouldn't happen after migration)
      return .ok spec
  return .error candidates

/-! ## Backward rule construction from specs -/

/--
Turn a spec proof `pre ⊑ wp prog post epost` into a backward rule proof term.

If `post` and/or `epost` are concrete (not top-level metavariables), fresh target metavariables
are introduced and the proof is generalized using `WPMonad.wp_cons_rel`, `WPMonad.wp_econs_rel`,
or `WPMonad.wp_econs_bot_rel`. If `pre` is concrete, it is generalized using `PartialOrder.rel_trans`.

The result stays in `⊑` form: `?pre s1..sn ⊑ wp prog ?post ?epost s1..sn`.
-/
private def mkSpecBackwardProof
    (pre rhs specProof : Expr) (ss _ssTypes : Array Expr) : SymM AbstractMVarsResult := do
  /- we start with `pre ⊑ wp prog post epost` where
  1. `pre` represents the Lean expression for `pre`
  2. `rhs` represents the Lean expression for `wp prog post epost`
  3. `specProof` represents the Lean expression for the proof of the spec `pre ⊑ wp prog post epost`
  4. `ss` represents the Lean expressions for the state variables `s1`, `s2`, ..., `sn`
  5. `_ssTypes` represents the Lean types for the state variables `s1`, `s2`, ..., `sn` -/
  let_expr wp _m _l _e _monadInst _instWP _α prog postSpec epostSpec := rhs
    | throwError "target not a wp application {rhs}"
  let mut postAbstract := postSpec.consumeMData
  let mut epostAbstract := epostSpec.consumeMData
  let mut specApplied := specProof

  /- abstract concrete `post` if it is not already abstract -/
  unless postAbstract.isMVar do
    /- `α → l`: type of `post` -/
    let postTy ← Sym.inferType postSpec
    /- mvar `postAbstract` for new abstract `post` -/
    postAbstract ← mkFreshExprMVar (userName := `post) postTy
    /- premise type `postSpec ⊑ postAbstract` for abstracting concrete `post` -/
    let hpostTy ← mkAppM ``PartialOrder.rel #[postSpec, postAbstract]
    /- mvar `?postImpl` for the proof of the premise -/
    let hpost ← mkFreshExprMVar (userName := `postImpl) hpostTy
    /- get the proof of `pre ⊑ wp prog postAbstract epostSpec`, where `post` is abstracted.
       Uses wp_cons_rel: post ⊑ post' → pre ⊑ wp x post epost → pre ⊑ wp x post' epost -/
    specApplied ← mkAppM ``WPMonad.wp_cons_rel #[prog, postSpec, postAbstract, epostSpec, hpost, specApplied]

  /- abstract concrete `epost` if it is not already abstract -/
  unless epostAbstract.isMVar do
    /- `EPost⟨t₁, t₂, ..., tₙ⟩`: type of `epost` -/
    let epostTy ← Sym.inferType epostSpec
    /- mvar `epostAbstract` for new abstract `epost` -/
    epostAbstract ← mkFreshExprMVar (userName := `epost) epostTy
    /- if `epost` is `⊥`, then `epost ⊑ epostAbstract` holds trivially and
      abstracting `epost` can be simply done by `WPMonad.wp_econs_bot_rel` without
      introducing a new premise. This case is quite common, that's why we handle
      it specially. -/
    let_expr bot _ _ := epostSpec |
      /- premise type `epostSpec ⊑ epostAbstract` for abstracting concrete `epost` -/
      let hepostTy ← mkAppM ``PartialOrder.rel #[epostSpec, epostAbstract]
      /- mvar `?epostImpl` for the proof of the premise -/
      let hepost ← mkFreshExprMVar (userName := `epostImpl) hepostTy
      /- get the proof of `pre ⊑ wp prog postAbstract epostAbstract`, where `epost` is abstracted.
        Uses wp_econs_rel: epost ⊑ epost' → pre ⊑ wp x post epost → pre ⊑ wp x post epost' -/
      specApplied ← mkAppM ``WPMonad.wp_econs_rel #[prog, postAbstract, epostSpec, epostAbstract, hepost, specApplied]
    /- get the proof of `pre ⊑ wp prog postAbstract epostAbstract`, where `epost (= ⊥)` is abstracted.
       This proof DOES NOT have a `?epostImpl` premise -/
    specApplied ← mkAppM ``WPMonad.wp_econs_bot_rel #[prog, postAbstract, epostAbstract, specApplied]

  /- At this point, `specApplied` has type `pre ⊑ wp prog ?postAbstract ?epostAbstract` at `l` level.
     Apply excess args to get pointwise form at `l'` level (where `l = S1 → ... → Sn → l'`):
     `specApplied s1..sn : pre s1..sn ⊑ wp prog ?postAbstract ?epostAbstract s1..sn` -/
  specApplied := mkAppN specApplied ss

  /- abstract concrete `pre` if it is not already abstract.
     Uses transitivity: `?preAbstract s1..sn ⊑ pre s1..sn ⊑ wp ... s1..sn`
     The premise `?preAbstract s1..sn ⊑ pre s1..sn` uses `PartialOrder.rel` at `l'` level
     (not `→`), since `l'` may not be `Prop`. -/
  let preAbstract := pre.consumeMData
  unless preAbstract.isMVar do
    let preTy ← Sym.inferType pre
    let preAbstract ← mkFreshExprMVar (userName := `pre) preTy
    /- no need for `betaRevS` on a fresh mvar — it cannot have betas -/
    let preAbstractApplied := mkAppN preAbstract ss
    /- use `betaRevS` to avoid creating beta redexes when `pre` is a lambda -/
    let preApplied ← betaRevS pre ss.reverse
    /- premise type `preAbstract s1..sn ⊑ pre s1..sn` at `l'` level -/
    let hpreRelTy ← mkAppM ``PartialOrder.rel #[preAbstractApplied, preApplied]
    /- mvar `?preImpl` for the proof of the premise -/
    let hpreRel ← mkFreshExprMVar (userName := `preImpl) hpreRelTy
    /- chain transitivity: ?preAbstract s1..sn ⊑ pre s1..sn ⊑ wp ... s1..sn -/
    specApplied ← mkAppM ``PartialOrder.rel_trans #[hpreRel, specApplied]

  abstractMVars specApplied

/--
Try to build a backward rule from a single spec theorem in `⊑` form.

Given a spec `pre ⊑ wp prog post epost` where the lattice type is
`l = σ1 → ... → σn → Prop`, produces an auxiliary lemma.

- `l`: the goal's lattice type (e.g. `Nat → Prop`)
- `instWP`: the `WPMonad` instance for the goal monad
- `excessArgs`: free variables representing state args from `l = σ1 → ... → σn → Prop`
-/
def tryMkBackwardRuleFromSpec (specThm : SpecTheorem)
  (l instWP : Expr) (excessArgs : Array Expr) : OptionT SymM BackwardRule := do
  -- Instantiate the spec theorem, creating metavars for all universally quantified params
  let (_xs, _bs, specProof, specType) ← specThm.proof.instantiate
  let_expr PartialOrder.rel l' _cl' pre rhs := specType
    | throwError "target not a partial order ⊑ application {specType}"
  guard <| ← isDefEqGuarded l l'
  let_expr wp _m' _ _ _monadInst' instWP' _α _e' _post _epost := rhs
    | throwError "target not a wp application {rhs}"
  guard <| ← isDefEqGuarded instWP instWP'
  -- Use local excess-state binders so explicit post premises can be re-lifted to `⊑`.
  let mut ss := #[]
  let mut ssTypes := #[]
  for arg in excessArgs do
    let ty ← Sym.inferType arg
    ssTypes := ssTypes.push ty
    ss := ss.push <| ← mkFreshExprMVar (userName := `s) ty
  let res ← mkSpecBackwardProof pre rhs specProof ss ssTypes
  let type ← preprocessExpr (← Meta.inferType res.expr)
  let spec ← Meta.mkAuxLemma res.paramNames.toList type res.expr
  mkBackwardRuleFromDecl spec

end Loom.Tactic.Spec
