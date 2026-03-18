/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vladimir Gladshtein, Sebastian Graf
-/
import Lean
import Loom.Tactic.Attr
import Loom.Tactic.Spec
import Loom.Tactic.ShareExt
import Lean.Meta.Match.Rewrite

open Lean Parser Meta Elab Tactic Sym Loom Lean.Order

namespace Loom.VCGen

open Lean.Elab.Tactic.Do in
/-- Creates a reusable backward rule for `ite`. Ported from VCGen.lean. -/
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
    -- Compute the base lattice type (e.g. Prop) for the `pre` variable
    let l' ← Sym.inferType (goalWithProg t)
    withLocalDeclD `pre l' fun pre => do
    -- Premises use `pre ⊑ wp branch ...` form
    let thenType ← mkArrow c (← mkAppM ``PartialOrder.rel #[pre, goalWithProg t])
    withLocalDeclD `hthen (← shareCommon thenType) fun hthen => do
    let elseType ← mkArrow (mkNot c) (← mkAppM ``PartialOrder.rel #[pre, goalWithProg e])
    withLocalDeclD `helse (← shareCommon elseType) fun helse => do
    let onAlt (hc : Expr) (hcase : Expr) := do
      let res ← rwIfWith hc prog
      if res.proof?.isNone then
        throwError "`rwIfWith` failed to rewrite {indentExpr prog}."
      let context ← withLocalDecl `x .default ma fun x => mkLambdaFVars #[x] (goalWithProg x)
      let res ← Simp.mkCongrArg context res
      res.mkEqMPR hcase
    -- Build inner proof: fun hpre : pre => dite ...
    -- hthen h : pre ⊑ wp t ... (def-eq to pre → wp t ...), so hthen h hpre : wp t ...
    withLocalDecl `hpre .default pre fun hpre => do
    let ht ← withLocalDecl `h .default c fun h => do
      mkLambdaFVars #[h] (← onAlt h (mkApp (mkApp hthen h) hpre))
    let he ← withLocalDecl `h .default (mkNot c) fun h => do
      mkLambdaFVars #[h] (← onAlt h (mkApp (mkApp helse h) hpre))
    let goalTy := goalWithProg prog
    let goalTySort ← Sym.inferType goalTy
    let u ←
      match goalTySort with
      | .sort lvl => pure lvl
      | _ => throwError "Expected sort for type {indentExpr goalTySort}"
    let innerPrf := mkApp5 (mkConst ``dite [u]) goalTy c dec ht he
    -- Wrap in lambda over hpre and annotate with PartialOrder.rel type
    let prf ← mkLambdaFVars #[hpre] innerPrf
    let relGoal ← mkAppM ``PartialOrder.rel #[pre, goalTy]
    let prf ← mkExpectedTypeHint prf relGoal
    mkLambdaFVars (#[a, c, dec, t, e] ++ ss ++ #[post, epost, pre, hthen, helse]) prf
  let res ← abstractMVars prf
  let type ← preprocessExpr (← Sym.inferType res.expr)
  let prf ← Meta.mkAuxLemma res.paramNames.toList type res.expr
  mkBackwardRuleFromDecl prf

end Loom.VCGen
