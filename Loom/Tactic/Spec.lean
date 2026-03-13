/-
Pattern-based spec theorem lookup and backward rule construction for VCGen'.
Contains the full FindSpec logic plus tryMkBackwardRuleFromSpec.
-/
import Lean
import Loom.Tactic.Attr
import Loom.Tactic.Logic
import Loom.Triple.Basic
import Loom.Triple.SpecLemmas

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
  trace[Loom.Tactic.vcgen] "Finding specs for {e}"
  let e ← instantiateMVars e
  -- Eta-reduce to match disc tree keys (patterns are preprocessed with etaReduceAll)
  let e ← shareCommon e
  let candidates := Sym.getMatch database.specs e

  trace[Loom.Tactic.vcgen] "Candidates: {candidates.map (·.proof.key)}"
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

/- TODO: what would the proper way? -/
private def mkStateName (_ty : Expr) : Name := `s
  -- match ty.const?.map (·.1) with
  -- | some name => "state" ++ name.toString |>.toName
  -- | none => `s

/-- Build the explicit pointwise implication premise used to weaken a concrete `post`. -/
private def mkPostPointwisePremise (postSpec postTarget postTy : Expr) (ssTypes : Array Expr) : SymM Expr := do
  let .forallE _ α _ _ := postTy
    | throwError "expected a postcondition function, got {indentExpr postTy}"
  withLocalDeclD `a α fun a => do
    let ssNamesTypes := ssTypes.map (fun ty => (mkStateName ty, ty))
    withLocalDeclsDND ssNamesTypes fun ss' => do
      let lhs := postSpec.betaRev <| ss'.reverse.push a
      let rhs := mkAppN (mkApp postTarget a) ss'
      mkForallFVars (#[a] ++ ss') (← mkAppM ``PartialOrder.rel  #[lhs, rhs])
/-- Recursively decompose `epostSpec ⊑ epostAbstract` into per-component proofs.
    - `EPost.cons.mk head tail` → mvar for `head ⊑ epostAbstract.head`, recurse on tail
    - `EPost.nil.mk` → trivial via `EPost.nil_rel`
    - Otherwise → single mvar for `epostSpec ⊑ epostAbstract` -/
partial def decomposeEPostRel (epostSpec epostAbstract : Expr) : SymM Expr := do
  match_expr epostSpec with
  | EPost.cons.mk ehTy _etTy head tail =>
    let absHead ← mkAppM ``EPost.cons.head #[epostAbstract]
    let absTail ← mkAppM ``EPost.cons.tail #[epostAbstract]
    let headTy ← Sym.inferType head
    -- Collect state types: e.g. String → Nat → Prop → skip first (exc type), rest are state types
    let ssTypes ← forallTelescope ehTy fun xs _ => do
      xs.drop 1 |>.mapM (Meta.inferType ·)
    let hHeadTy ← mkPostPointwisePremise head absHead headTy ssTypes
    let hHead ← mkFreshExprMVar (userName := `epostImpl) hHeadTy
    let hTail ← decomposeEPostRel tail absTail
    mkAppM ``EPost.cons_rel #[head, tail, epostAbstract, hHead, hTail]
  | EPost.nil.mk =>
    mkAppM ``EPost.nil_rel #[epostAbstract]
  | _ =>
    let hTy ← mkAppM ``PartialOrder.rel #[epostSpec, epostAbstract]
    let h ← mkFreshExprMVar (userName := `epostImpl) hTy
    return h

/--
Turn a spec proof `pre ⊑ wp prog post epost` into a backward rule proof term.

If `post` and/or `epost` are concrete (not top-level metavariables), fresh target metavariables
are introduced and the proof is generalized using `WPMonad.wp_cons_rel`, `WPMonad.wp_econs_rel`,
or `WPMonad.wp_econs_bot_rel`. If `pre` is concrete, it is generalized using `PartialOrder.rel_trans`.

The result stays in `⊑` form: `?pre s1..sn ⊑ wp prog ?post ?epost s1..sn`.
-/
private def mkSpecBackwardProof
    (pre rhs specProof : Expr) (ss ssTypes : Array Expr) : SymM AbstractMVarsResult := do
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
    /- premise type `∀ (a : α) (s₁ : σ₁) ... (sₙ : σₙ), postSpec a s₁ ... sₙ → postAbstract a s₁ ... sₙ` -/
    let hpostTy ← mkPostPointwisePremise postSpec postAbstract postTy ssTypes
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
      /- Decompose `epostSpec ⊑ epostAbstract` into per-component proofs
        using `EPost.cons_rel` and `EPost.nil_rel` -/
      let hepost ← decomposeEPostRel epostSpec epostAbstract
      specApplied ← mkAppM ``WPMonad.wp_econs_rel #[prog, postAbstract, epostSpec, epostAbstract, hepost, specApplied]
    /- get the proof of `pre ⊑ wp prog postAbstract epostAbstract`, where `epost (= ⊥)` is abstracted.
       This proof DOES NOT have a `?epostImpl` premise -/
    specApplied ← mkAppM ``WPMonad.wp_econs_bot_rel #[prog, postAbstract, epostAbstract, specApplied]

  let preApplied ← betaRevS pre ss.reverse
  specApplied := mkAppN specApplied ss
  let wpTy ← mkAppM ``wp <| #[prog, postAbstract, epostAbstract] ++ ss
  let specAppliedTy ← mkAppM ``PartialOrder.rel #[preApplied, wpTy]
  specApplied ← mkExpectedTypeHint specApplied specAppliedTy
  /- use `betaRevS` to avoid creating beta redexes when `pre` is a lambda -/
  let preAppliedTy ← Meta.inferType preApplied
  let preAbstract ← mkFreshExprMVar (userName := `pre) preAppliedTy
  let specAbstractTy ← mkAppM ``PartialOrder.rel #[preAbstract, preApplied]
  let specAbstract ← mkFreshExprMVar (userName := `vc) specAbstractTy
  specApplied ← mkAppM ``PartialOrder.rel_trans #[specAbstract, specApplied]

  /- At this point, `specApplied` has type `pre ⊑ wp prog ?postAbstract ?epostAbstract` at `l` level.
     Apply excess args to get pointwise form at `l'` level (where `l = S1 → ... → Sn → l'`):
     `specApplied s1..sn : pre s1..sn ⊑ wp prog ?postAbstract ?epostAbstract s1..sn` -/
  -- specApplied := mkAppN specApplied ss
  -- let wpTy ← mkAppM ``wp <| #[prog, postAbstract, epostAbstract] ++ ss
  -- let specAppliedTy ← mkAppM ``PartialOrder.rel #[preApplied, wpTy]
  -- specApplied ← mkExpectedTypeHint specApplied specAppliedTy

  /- abstract concrete `pre` if it is not already abstract.
     Uses transitivity: `?preAbstract s1..sn ⊑ pre s1..sn ⊑ wp ... s1..sn`
     The premise `?preAbstract s1..sn ⊑ pre s1..sn` uses `PartialOrder.rel` at `l'` level
     (not `→`), since `l'` may not be `Prop`. -/
  -- unless preAbstract.isMVar do
  --   let preTy ← Sym.inferType pre
  --   let preAbstract ← mkFreshExprMVar (userName := `pre) preTy
  --   /- no need for `betaRevS` on a fresh mvar — it cannot have betas -/
  --   let preAbstractApplied := mkAppN preAbstract ss
  --   /- premise type `preAbstract s1..sn ⊑ pre s1..sn` at `l'` level -/
  --   let hpreRelTy ← mkAppM ``PartialOrder.rel #[preAbstractApplied, preApplied]
  --   /- mvar `?preImpl` for the proof of the premise -/
  --   let hpreRel ← mkFreshExprMVar (userName := `preImpl) hpreRelTy
  --   /- chain transitivity: ?preAbstract s1..sn ⊑ pre s1..sn ⊑ wp ... s1..sn -/
  --   specApplied ← mkAppOptM ``PartialOrder.rel_trans #[none, none, none, none, wpTy, hpreRel, specApplied]

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

/-! ## Tests for mkSpecBackwardProof -/

section Test

/-- Test helper: call mkSpecBackwardProof directly and return the type of the result.
    Mirrors `testSpecBackwardProofType` from VCGen.lean but for the new ⊑-form output. -/
private def testSpecBackwardProofType' (declName : Name)
    (excessArgTypes : Array Expr) : MetaM Expr := do
  let specThm ← mkSpecTheoremFromConst declName
  let (_xs, _bs, specProof, specType) ← specThm.proof.instantiate
  let_expr PartialOrder.rel _ _ pre rhs := specType
    | throwError "not a partial order ⊑ application {specType}"
  let excessArgNamesTypes := excessArgTypes.map fun ty => (`s, ty)
  let spec ← withLocalDeclsDND excessArgNamesTypes fun ss => do
    let res ← SymM.run <| mkSpecBackwardProof pre rhs specProof ss excessArgTypes
    mkLambdaFVars ss res.expr
  instantiateMVars (← inferType spec)

/-- Test helper: call tryMkBackwardRuleFromSpec and return the backward rule type. -/
private def testBackwardRule' (declName : Name) (l instWP : Expr)
    (excessArgs : Array Expr) : MetaM Expr := do
  let specThm ← mkSpecTheoremFromConst declName
  let rule ← SymM.run do
    tryMkBackwardRuleFromSpec specThm l instWP excessArgs
  match rule with
  | some br => inferType br.expr
  | none => throwError "tryMkBackwardRuleFromSpec returned none for {declName}"

-- Test 1': wp_bind for Id, n=0 excess args (abstract pre/post/epost)
#eval! show MetaM Unit from do
  let m := mkConst ``Id [.zero]
  let l := mkSort 0
  let errTy := mkConst ``EPost.nil
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero, .zero]) #[m, l, errTy, monadM])
  let ty ← testBackwardRule' ``WPMonad.wp_bind l instWP #[]
  logInfo m!"Test 1' (Id, n=0): {ty}"

-- Test 2': wp_bind for StateM Nat, n=1 excess arg
#eval! show MetaM Unit from do
  let nat := mkConst ``Nat
  let m ← mkAppM ``StateM #[nat]
  let l ← mkArrow nat (mkSort 0)
  let errTy := mkConst ``EPost.nil
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero, .zero]) #[m, l, errTy, monadM])
  withLocalDeclD `s nat fun s => do
    let ty ← testBackwardRule' ``WPMonad.wp_bind l instWP #[s]
    logInfo m!"Test 2' (StateM Nat, n=1): {ty}"

-- Test A': concrete post, 1 excess arg
@[local lspec high]
theorem spec_set_concretePost_test' (epost : EPost.nil) :
    wp (set (m := StateM Nat) 7) (fun _ _ => True) epost ⊑
      wp (set (m := StateM Nat) 7) (fun _ _ => True) epost := by
  exact PartialOrder.rel_refl

#eval! show MetaM Unit from do
  let nat := mkConst ``Nat
  let ty ← testSpecBackwardProofType' ``spec_set_concretePost_test' #[nat]
  logInfo m!"Test A' (concrete post, n=1): {ty}"

-- Test B': concrete epost (non-⊥), 0 excess args
@[local lspec high]
theorem spec_throw_concreteEPost_test' (post : PUnit → Prop) :
    wp (MonadExceptOf.throw "boom" : Except String PUnit) post epost⟨fun _ => True⟩ ⊑
      wp (MonadExceptOf.throw "boom" : Except String PUnit) post epost⟨fun _ => True⟩ := by
  exact PartialOrder.rel_refl

#eval! show MetaM Unit from do
  let ty ← testSpecBackwardProofType' ``spec_throw_concreteEPost_test' #[]
  logInfo m!"Test B' (concrete epost, n=0): {ty}"

-- Test C': concrete post + epost, 0 excess args
@[local lspec high]
theorem spec_throw_concretePostEPost_test' :
    wp (MonadExceptOf.throw "boom" : Except String PUnit) (fun _ => True) epost⟨fun _ => True⟩ ⊑
      wp (MonadExceptOf.throw "boom" : Except String PUnit) (fun _ => True) epost⟨fun _ => True⟩ := by
  exact PartialOrder.rel_refl

#eval! show MetaM Unit from do
  let ty ← testSpecBackwardProofType' ``spec_throw_concretePostEPost_test' #[]
  logInfo m!"Test C' (concrete post+epost, n=0): {ty}"

-- Test D': nested concrete epost, 0 excess args
@[local lspec high]
theorem spec_throw_nestedConcreteEPost_test' (post : PUnit → Prop) :
    wp (MonadExceptOf.throw 7 : ExceptT Nat (Except String) PUnit) post
      epost⟨fun n => n = 7, fun s => s = "inner"⟩ ⊑
    wp (MonadExceptOf.throw 7 : ExceptT Nat (Except String) PUnit) post
      epost⟨fun n => n = 7, fun s => s = "inner"⟩ := by
  exact PartialOrder.rel_refl

#eval! show MetaM Unit from do
  let ty ← testSpecBackwardProofType' ``spec_throw_nestedConcreteEPost_test' #[]
  logInfo m!"Test D' (nested epost, n=0): {ty}"

-- Test E': ⊥ epost, 0 excess args (should have no epost premise)
@[local lspec high]
theorem spec_throw_botEPost_test' (post : PUnit → Prop) :
    wp (MonadExceptOf.throw "boom" : Except String PUnit) post (⊥ : EPost⟨String → Prop⟩) ⊑
      wp (MonadExceptOf.throw "boom" : Except String PUnit) post (⊥ : EPost⟨String → Prop⟩) := by
  exact PartialOrder.rel_refl

#eval! show MetaM Unit from do
  let ty ← testSpecBackwardProofType' ``spec_throw_botEPost_test' #[]
  logInfo m!"Test E' (bot epost, n=0): {ty}"

-- Test F': Spec.get_StateT for StateM Nat (abstract post/epost, concrete pre)
@[local lspec high]
theorem spec_get_StateM_test' (post : Nat → Nat → Prop) (epost : EPost.nil) :
    (fun s => post s s) ⊑ wp (MonadStateOf.get : StateM Nat Nat) post epost :=
  Triple.iff.mp (Spec.get_StateT post)

#eval! show MetaM Unit from do
  let nat := mkConst ``Nat
  let m ← mkAppM ``StateM #[nat]
  let l ← mkArrow nat (mkSort 0)
  let errTy := mkConst ``EPost.nil
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero, .zero]) #[m, l, errTy, monadM])
  withLocalDeclD `s nat fun s => do
    let ty ← testBackwardRule' ``spec_get_StateM_test' l instWP #[s]
    logInfo m!"Test F' (get_StateT, StateM Nat, n=1): {ty}"

-- Test G': Spec.set_StateT for StateM Nat (abstract post/epost, concrete pre)
@[local lspec high]
theorem spec_set_StateM_test' (v : Nat) (post : PUnit → Nat → Prop) (epost : EPost.nil) :
    (fun _ => post ⟨⟩ v) ⊑ wp (set v : StateM Nat PUnit) post epost :=
  Triple.iff.mp (Spec.set_StateT v post)

#eval! show MetaM Unit from do
  let nat := mkConst ``Nat
  let m ← mkAppM ``StateM #[nat]
  let l ← mkArrow nat (mkSort 0)
  let errTy := mkConst ``EPost.nil
  let monadM ← synthInstance (← mkAppM ``Monad #[m])
  let instWP ← synthInstance (mkAppN (mkConst ``WPMonad [.zero, .zero, .zero, .zero]) #[m, l, errTy, monadM])
  withLocalDeclD `s nat fun s => do
    let ty ← testBackwardRule' ``spec_set_StateM_test' l instWP #[s]
    logInfo m!"Test G' (set_StateT, StateM Nat, n=1): {ty}"

-- Test H': nested epost with state args (exercises ssTypes in decomposeEPostRel)
abbrev M_test := ExceptT Nat (ExceptT String (StateM Nat))

@[local lspec high]
theorem spec_throw_nestedEPostWithState_test' (post : PUnit → Nat → Prop) :
    wp (MonadExceptOf.throw 7 : M_test PUnit) post
      epost⟨fun n s => n = 7 ∧ s = 0, fun e s => e = "inner" ∧ s = 0⟩ ⊑
    wp (MonadExceptOf.throw 7 : M_test PUnit) post
      epost⟨fun n s => n = 7 ∧ s = 0, fun e s => e = "inner" ∧ s = 0⟩ := by
  exact PartialOrder.rel_refl

#eval! show MetaM Unit from do
  let nat := mkConst ``Nat
  let ty ← testSpecBackwardProofType' ``spec_throw_nestedEPostWithState_test' #[nat]
  logInfo m!"Test H' (nested epost with state, n=1): {ty}"

end Test

end Loom.Tactic.Spec
