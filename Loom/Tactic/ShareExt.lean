import Lean

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
private def instantiateRangeS' (e : Expr) (beginIdx endIdx : Nat) (subst : Array Expr) : AlphaShareBuilderM Expr :=
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
private def instantiateS' (e : Expr) (subst : Array Expr) : AlphaShareBuilderM Expr :=
  instantiateRangeS' e 0 subst.size subst

/--
Similar to `Lean.Expr.instantiate`.
It assumes the input is maximally shared, and ensures the output is too.
-/
private def instantiateS  (e : Expr) (subst : Array Expr) : SymM Expr :=
  liftBuilderM <| instantiateS' e subst

/--
Beta-reduces `f` applied to reversed arguments `revArgs`, ensuring maximally shared terms.
`betaRevS f #[a₃, a₂, a₁]` computes the beta-normal form of `f a₁ a₂ a₃`.
-/
private partial def betaRevS' (f : Expr) (revArgs : Array Expr) : AlphaShareBuilderM Expr :=
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

public def betaRevS (f : Expr) (revArgs : Array Expr) : SymM Expr :=
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

namespace Loom

def preprocessExpr (e : Expr) : SymM Expr := do
  shareCommon (← unfoldReducible (← instantiateMVars e))

end Loom
