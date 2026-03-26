/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
module

prelude
public import Lean
public meta import Lean.Meta.Sym.AlphaShareBuilder
public meta import Lean.Meta.Sym.LooseBVarsS
public meta import Lean.Meta.Sym.Grind
public meta import Loom.Tactic.VCGenTime

public section

open Lean Parser Meta Elab Tactic Sym Lean.Order

open Sym Sym.Internal

-- The following function is vendored until it is made public:
/-- `mkAppRevRangeS f b e args == mkAppRev f (revArgs.extract b e)` -/
meta def mkAppRevRangeS [Monad m] [Internal.MonadShareCommon m] (f : Expr) (beginIdx endIdx : Nat) (revArgs : Array Expr) : m Expr :=
  loop revArgs beginIdx f endIdx
where
  loop (revArgs : Array Expr) (start : Nat) (b : Expr) (i : Nat) : m Expr := do
  if i ≤ start then
    return b
  else
    let i := i - 1
    loop revArgs start (← mkAppS b revArgs[i]!) i

/--
Similar to `Lean.Expr.instantiateRange`.
It assumes the input is maximally shared, and ensures the output is too.
It assumes `beginIdx ≤ endIdx` and `endIdx ≤ subst.size`
-/
private meta def instantiateRangeS' (e : Expr) (beginIdx endIdx : Nat) (subst : Array Expr) : AlphaShareBuilderM Expr :=
  if _ : beginIdx > endIdx then unreachable! else
  if _ : endIdx > subst.size then unreachable! else
  let n := endIdx - beginIdx
  replaceS' e fun e offset => do
    match e with
    | .bvar idx =>
      if _h : idx >= offset then
        if _h : idx < offset + n then
          let v := subst[beginIdx + idx - offset]
          liftLooseBVarsS' v 0 offset
        else
          mkBVarS (idx - n)
      else
        return some e
    | .lit _ | .mvar _ | .fvar _ | .const _ _ | .sort _ =>
      return some e
    | _ =>
      if offset >= e.looseBVarRange then
        return some e
      else
        return none

/-- Internal variant of `instantiateS` that runs in `AlphaShareBuilderM`. -/
private meta def instantiateS' (e : Expr) (subst : Array Expr) : AlphaShareBuilderM Expr :=
  instantiateRangeS' e 0 subst.size subst

/--
Similar to `Lean.Expr.instantiate`.
It assumes the input is maximally shared, and ensures the output is too.
-/
private meta def instantiateS  (e : Expr) (subst : Array Expr) : SymM Expr :=
  liftBuilderM <| instantiateS' e subst

/--
Beta-reduces `f` applied to reversed arguments `revArgs`, ensuring maximally shared terms.
`betaRevS f #[a₃, a₂, a₁]` computes the beta-normal form of `f a₁ a₂ a₃`.
-/
private meta partial def betaRevS' (f : Expr) (revArgs : Array Expr) : AlphaShareBuilderM Expr :=
  if revArgs.size == 0 then
    return f
  else
    let sz := revArgs.size
    let rec go (e : Expr) (i : Nat) : AlphaShareBuilderM Expr := do
      match e with
      | .lam _ _ b _ =>
        if i + 1 < sz then
          go b (i+1)
        else
          instantiateS' b revArgs
      | .mdata _ b => go b i
      | _ =>
        let n := sz - i
        mkAppRevRangeS (← instantiateRangeS' e n sz revArgs) 0 n revArgs
    go f 0

public meta def betaRevS (f : Expr) (revArgs : Array Expr) : SymM Expr :=
  liftBuilderM <| betaRevS' f revArgs


meta def mkAppRevS [Monad m] [Internal.MonadShareCommon m] (f : Expr) (revArgs : Array Expr) : m Expr :=
  mkAppRevRangeS f 0 revArgs.size revArgs


meta def mkAppRangeS [Monad m] [Internal.MonadShareCommon m] (f : Expr) (beginIdx endIdx : Nat) (args : Array Expr) : m Expr :=
  loop args endIdx f beginIdx
where
  loop (args : Array Expr) (end' : Nat) (b : Expr) (i : Nat) : m Expr := do
  if end' ≤ i then
    return b
  else
    loop args end' (← mkAppS b args[i]!) (i + 1)

meta def mkAppNS [Monad m] [Internal.MonadShareCommon m] (f : Expr) (args : Array Expr) : m Expr :=
  mkAppRangeS f 0 args.size args


meta def mkAppS₆ [Monad m] [Internal.MonadShareCommon m] (f a₁ a₂ a₃ a₄ a₅ a₆ : Expr) : m Expr := do
  mkAppS (← mkAppS₅ f a₁ a₂ a₃ a₄ a₅) a₆

meta def mkAppS₇ [Monad m] [Internal.MonadShareCommon m] (f a₁ a₂ a₃ a₄ a₅ a₆ a₇ : Expr) : m Expr := do
  mkAppS (← mkAppS₆ f a₁ a₂ a₃ a₄ a₅ a₆) a₇

meta def mkAppS₈ [Monad m] [Internal.MonadShareCommon m] (f a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : Expr) : m Expr := do
  mkAppS (← mkAppS₇ f a₁ a₂ a₃ a₄ a₅ a₆ a₇) a₈

meta def mkAppS₉ [Monad m] [Internal.MonadShareCommon m] (f a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ : Expr) : m Expr := do
  mkAppS (← mkAppS₈ f a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) a₉

meta def mkAppS₁₀ [Monad m] [Internal.MonadShareCommon m] (f a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ : Expr) : m Expr := do
  mkAppS (← mkAppS₉ f a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) a₁₀

meta def mkAppS₁₁ [Monad m] [Internal.MonadShareCommon m] (f a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀ a₁₁ : Expr) : m Expr := do
  mkAppS (← mkAppS₁₀ f a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ a₁₀) a₁₁

namespace Loom

/--
Returns `true` if `declName` is the name of a grind helper declaration that
should not be unfolded by `unfoldReducible`.
-/
def isGrindGadget (declName : Name) : Bool :=
  declName == ``Grind.EqMatch

/-
Auxiliary function for implementing `unfoldReducible` and `unfoldReducibleSimproc`.
Performs a single step.
-/
def unfoldReducibleStepEta (e : Expr) : MetaM TransformStep := do
  let .const declName _ := e.getAppFn | return .continue
  unless (← isReducible declName) do return .continue
  if isGrindGadget declName then return .continue
  -- See comment at isUnfoldReducibleTarget.
  if (← getEnv).isProjectionFn declName then return .continue
  let some v ← unfoldDefinition? e | return .continue
  return .visit v

def isUnfoldReducibleTargetEta (e : Expr) : CoreM Bool := do
  let env ← getEnv
  return Option.isSome <| e.find? fun e => Id.run do
    let .const declName _ := e | return false
    if getReducibilityStatusCore env declName matches .reducible then
      -- Remark: it is wasteful to unfold projection functions since
      -- kernel projections are folded again in the `foldProjs` preprocessing step.
      return !isGrindGadget declName && !env.isProjectionFn declName
    else
      return false

/--
Unfolds all `reducible` declarations occurring in `e`.
This is meant as a preprocessing step. It does **not** guarantee maximally shared terms
-/
public def unfoldReducibleEta (e : Expr) : MetaM Expr := do
  if !(← isUnfoldReducibleTargetEta e) then return e
  Meta.transform e (pre := unfoldReducibleStepEta)

/--
Instantiates metavariables, unfold reducible, and applies `shareCommon`.
-/
def preprocessExpr (e : Expr) : SymM Expr := do
  shareCommon (← unfoldReducibleEta (← instantiateMVars e))

end Loom

open Lean Meta Grind in
/-- Like `internalizeAll`, but records timing when `vcgen.time` is set. -/
public meta def Lean.Meta.Grind.Goal.timedInternalizeAll (goal : Grind.Goal) : GrindM Grind.Goal := do
  let g ← if Loom.vcgen.time.get (← getOptions) then do
    let (g, ns) ← Loom.timeNs goal.internalizeAll
    Loom.addInternalizeTime ns
    pure g
  else
    goal.internalizeAll
  pure g

open Lean Meta Grind in
/-- Like `grind`, but records timing when `vcgen.time` is set. -/
public meta def Lean.Meta.Grind.Goal.timedGrind (goal : Grind.Goal) : GrindM GrindResult := do
  if Loom.vcgen.time.get (← getOptions) then
    let (res, ns) ← Loom.timeNs goal.grind
    Loom.addGrindSolveTime ns
    pure res
  else
    goal.grind

open Lean Meta Grind in
/-- Try to discharge `goal` with grind. `internalizeAll` reassigns the goal's
    mvar to a fresh metavar; if grind fails we restore the MCtx so the
    proof term built by the caller stays intact.
    Returns `none` if grind closed the goal, or `some mvarId` for the unsolved goal. -/
public meta def Lean.Meta.Grind.Goal.timedTryGrind (goal : Grind.Goal) : GrindM (Option MVarId) := do
  let savedMCtx ← getMCtx
  let goal ← goal.timedInternalizeAll
  match ← goal.timedGrind with
  | .closed => return none
  | .failed .. =>
    setMCtx savedMCtx
    return some goal.mvarId

end -- public section
