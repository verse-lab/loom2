import Lean.Elab.Tactic
import Lean.Meta
import Lean.PrettyPrinter

import Loom.Instances.SepLogFracWithoutAxiom

open Lean Elab Tactic Meta Term PrettyPrinter
open Loom
open Lean.Order Loom

namespace Loom
namespace Perm

def remainder (π : _root_.Perm) (h : π.val < 1) : _root_.Perm :=
  ⟨1 - π.val, by grind⟩

@[simp] theorem remainder_val (π : _root_.Perm) (h : π.val < 1) :
    (Perm.remainder π h).val = 1 - π.val := rfl

theorem remainder_isValid (π : _root_.Perm) (h : π.val < 1) :
    (Perm.remainder π h).IsValid := by
  show (1 - π.val) ≤ 1; grind

theorem add_remainder_eq_one (π : _root_.Perm) (h : π.val < 1) :
    π + Perm.remainder π h = 1 := by
  ext; change π.val + (1 - π.val) = (1 : Rat); grind

def diff (π_have π_exhale : _root_.Perm) (h : π_exhale.val < π_have.val) : _root_.Perm :=
  ⟨π_have.val - π_exhale.val, by grind⟩

@[simp] theorem diff_val (π_have π_exhale : _root_.Perm) (h : π_exhale.val < π_have.val) :
    (Perm.diff π_have π_exhale h).val = π_have.val - π_exhale.val := rfl

theorem diff_isValid (π_have π_exhale : _root_.Perm)
    (h : π_exhale.val < π_have.val) (hv_have : π_have.IsValid) :
    (Perm.diff π_have π_exhale h).IsValid := by
  show π_have.val - π_exhale.val ≤ 1
  unfold _root_.Perm.IsValid at hv_have
  have : π_have.val ≤ 1 := hv_have; grind

theorem add_diff_eq_have (π_have π_exhale : _root_.Perm) (h : π_exhale.val < π_have.val) :
    π_exhale + Perm.diff π_have π_exhale h = π_have := by
  ext; change π_exhale.val + (π_have.val - π_exhale.val) = π_have.val; grind

end Perm

namespace HeapM

theorem triple_exhale_full {P : hProp} {rest : HeapM α} {Q : α → hProp}
    (x : Loc) (v : Val)
    (hpre : P = x ↦ v)
    (h : ⦃ ∅ ⦄ rest ⦃ Q ⦄) :
    ⦃ P ⦄ (do HeapM.exhale (x ↦[1] v); rest) ⦃ Q ⦄ := by
  apply HeapM.triple_exhale (R := ∅)
  · rw [hpre, hSingle_eq_hSingleFrac, hStar_empty]
  · exact h

theorem triple_exhale_frac_lt_one
    {P : hProp} {rest : HeapM α} {Q : α → hProp}
    (x : Loc) (v : Val) (π_exhale : _root_.Perm)
    (hlt : π_exhale.val < 1)
    (hv_exhale : π_exhale.IsValid)
    (hpre : P = x ↦ v)
    (h : ⦃ x ↦[Perm.remainder π_exhale hlt] v ⦄ rest ⦃ Q ⦄) :
    ⦃ P ⦄ (do HeapM.exhale (x ↦[π_exhale] v); rest) ⦃ Q ⦄ := by
  apply HeapM.triple_exhale_frac x v π_exhale (Perm.remainder π_exhale hlt)
  · exact hv_exhale
  · exact Perm.remainder_isValid π_exhale hlt
  · exact Perm.add_remainder_eq_one π_exhale hlt
  · exact hpre
  · exact h

theorem triple_exhale_frac_of_frac_lt
    {P : hProp} {rest : HeapM α} {Q : α → hProp}
    (x : Loc) (v : Val) (π_have π_exhale : _root_.Perm)
    (hlt : π_exhale.val < π_have.val)
    (hv_exhale : π_exhale.IsValid)
    (hv_have : π_have.IsValid)
    (hpre : P = x ↦[π_have] v)
    (h : ⦃ x ↦[Perm.diff π_have π_exhale hlt] v ⦄ rest ⦃ Q ⦄) :
    ⦃ P ⦄ (do HeapM.exhale (x ↦[π_exhale] v); rest) ⦃ Q ⦄ := by
  apply HeapM.triple_exhale_frac_of_frac x v π_have π_exhale (Perm.diff π_have π_exhale hlt)
  · exact hv_exhale
  · exact Perm.diff_isValid π_have π_exhale hlt hv_have
  · exact Perm.add_diff_eq_have π_have π_exhale hlt
  · exact hv_have
  · exact hpre
  · exact h

end HeapM


structure SChunk where
  loc : Expr
  val : Expr
  perm : Option Expr
  deriving Inhabited

abbrev SHeap := List SChunk

def matchHSingle? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← whnfR e
  if e.isAppOfArity ``hSingle 2 then
    return some (e.getArg! 0, e.getArg! 1)
  else
    return none

def matchHSingleFrac? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let e ← whnfR e
  if e.isAppOfArity ``hSingleFrac 3 then
    return some (e.getArg! 0, e.getArg! 1, e.getArg! 2)
  else
    return none

def parseChunk? (e : Expr) : MetaM (Option SChunk) := do
  if let some (loc, val) ← matchHSingle? e then
    return some ⟨loc, val, none⟩
  else if let some (loc, val, perm) ← matchHSingleFrac? e then
    return some ⟨loc, val, some perm⟩
  else
    return none

def isEmptyProp? (e : Expr) : MetaM Bool := do
  let e ← whnfR e
  if e.isAppOfArity ``EmptyCollection.emptyCollection 2 then return true
  if e.isAppOfArity ``hEmpty 0 then return true
  return false

partial def parsePrecond (e : Expr) : MetaM SHeap := do
  let e ← whnfR e
  if e.hasMVar then
    throwError "err: {e}"
  if ← isEmptyProp? e then
    return []
  else if let some chunk ← parseChunk? e then
    return [chunk]
  else if e.isAppOfArity ``hStar 2 then
    let h1 := e.getArg! 0
    let h2 := e.getArg! 1
    let c1 ← parsePrecond h1
    let c2 ← parsePrecond h2
    return c1 ++ c2
  else
    throwError "err: {e}"

def findChunk (heap : SHeap) (loc val : Expr) : MetaM (Option (Nat × SChunk × SHeap)) := do
  for i in [:heap.length] do
    let chunk := heap[i]!
    let locEq ← isDefEq chunk.loc loc
    let valEq ← isDefEq chunk.val val
    if locEq && valEq then
      let remaining := heap.eraseIdx i
      return some (i, chunk, remaining)
  return none

def exprToSyntax' (e : Expr) : TacticM Syntax.Term := do
  let stx ← delab e
  return stx


partial def symexecCore : TacticM Unit := symexecLoop
where
  symexecLoop : TacticM Unit := do
    let goal ← getMainGoal
    let goalType ← goal.getType
    let goalType ← instantiateMVars goalType

    let fn := goalType.getAppFn
    if !(fn.isConst && fn.constName! == ``Loom.Triple) then return

    let args := goalType.getAppArgs
    let numArgs := args.size
    let pre := args[numArgs - 4]!
    let code := args[numArgs - 3]!
    let code ← whnfR code

    if code.isAppOfArity ``Bind.bind 6 then
      let m1 := code.getArg! 4
      let m1 ← whnfR m1

      if m1.isAppOfArity ``HeapM.inhale 1 then
        evalTactic (← `(tactic| apply HeapM.triple_inhale))
        trySimplifyPre
        symexecLoop
      else if m1.isAppOfArity ``HeapM.exhale 1 then
        let prop := m1.getArg! 0
        let some exhaleChunk ← parseChunk? prop
          | throwError "err: {prop}"
        processExhale pre exhaleChunk
        symexecLoop
      else
        throwError "err: {m1}"

    else if code.isAppOfArity ``HeapM.skip 0 then
      evalTactic (← `(tactic|
        first
        | exact Triple.pure () PartialOrder.rel_refl
        | (apply Triple.pure ()
           simp only [PartialOrder.rel, Loom.Perm.remainder, Loom.Perm.diff]
           grind)))

    else if code.isAppOfArity ``Pure.pure 4 then
      evalTactic (← `(tactic| exact Triple.pure () PartialOrder.rel_refl))

    else if code.isAppOfArity ``HeapM.inhale 1 then
      evalTactic (← `(tactic| apply HeapM.triple_inhale_done))

    else if code.isAppOfArity ``HeapM.exhale 1 then
      let prop := code.getArg! 0
      let some exhaleChunk ← parseChunk? prop
        | throwError "err {prop}"
      processExhale pre exhaleChunk

    else
      throwError "err: {code}"

  trySimplifyPre : TacticM Unit := do
    try evalTactic (← `(tactic| apply HeapM.triple_pre_eq; simp; rfl))
    catch _ => pure ()

  processExhale (pre : Expr) (exhaleChunk : SChunk) : TacticM Unit := do
    let preChunks ← parsePrecond pre
    let some (_, matchedChunk, _) ← findChunk preChunks exhaleChunk.loc exhaleChunk.val
      | throwError "err"
    let preStx ← exprToSyntax' pre

    match matchedChunk.perm, exhaleChunk.perm with
    | none, some exhPerm =>
      let loc ← exprToSyntax' exhaleChunk.loc
      let val ← exprToSyntax' exhaleChunk.val
      let exhPermStx ← exprToSyntax' exhPerm
      if preChunks.length == 1 then
        evalTactic (← `(tactic|
          first
          | apply (HeapM.triple_exhale_full (P := $preStx) $loc $val rfl)
          | apply (HeapM.triple_exhale_frac_lt_one (P := $preStx) $loc $val $exhPermStx
              (by simp [Loom.Perm.remainder, Loom.Perm.diff, _root_.Perm.IsValid, _root_.Perm.le_def]; grind)
              (by simp [Loom.Perm.remainder, Loom.Perm.diff, _root_.Perm.IsValid, _root_.Perm.le_def]; grind)
              rfl)))
      else
        throwError "err"

    | some havePerm, some exhPerm =>
      let loc ← exprToSyntax' exhaleChunk.loc
      let val ← exprToSyntax' exhaleChunk.val
      let havePermStx ← exprToSyntax' havePerm
      let exhPermStx ← exprToSyntax' exhPerm
      if preChunks.length == 1 then
        evalTactic (← `(tactic|
          apply (HeapM.triple_exhale_frac_of_frac_lt (P := $preStx) $loc $val $havePermStx $exhPermStx
            (by simp [Loom.Perm.remainder, Loom.Perm.diff, _root_.Perm.IsValid, _root_.Perm.le_def]; grind)
            (by simp [Loom.Perm.remainder, Loom.Perm.diff, _root_.Perm.IsValid, _root_.Perm.le_def]; grind)
            (by simp [Loom.Perm.remainder, Loom.Perm.diff, _root_.Perm.IsValid, _root_.Perm.le_def]; grind)
            rfl)))
      else
        throwError "error"

    | none, none =>
      throwError "error"
    | some _, none =>
      throwError "error"

elab "symexec" : tactic => symexecCore


example (p : Loc) (v : Val) :
    ⦃ ∅ ⦄
    (do HeapM.inhale (p ↦ v)
        HeapM.exhale (p ↦[Perm.third] v)
        HeapM.skip)
    ⦃ _, p ↦[Perm.twoThirds] v ⦄ := by
  symexec

  example (p : Loc) (v : Val) :
    ⦃ p ↦ v ⦄
    (do
        HeapM.exhale (p ↦[Perm.third] v)
        HeapM.skip)
    ⦃ _, p ↦[Perm.twoThirds] v ⦄ := by
  symexec


example (p : Loc) (v : Val) :
    ⦃ ∅ ⦄
    (do HeapM.inhale (p ↦ v)
        HeapM.exhale (p ↦[Perm.third] v)
        HeapM.exhale (p ↦[Perm.third] v)
        HeapM.skip)
    ⦃ _, p ↦[Perm.third] v ⦄ := by
  symexec
