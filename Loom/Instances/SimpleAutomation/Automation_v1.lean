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
  ⟨1 - π.val, by
    grind⟩

@[simp] theorem remainder_val (π : _root_.Perm) (h : π.val < 1) :
    (Perm.remainder π h).val = 1 - π.val := rfl

theorem remainder_isValid (π : _root_.Perm) (h : π.val < 1) :
    (Perm.remainder π h).IsValid := by
  show (1 - π.val) ≤ 1
  grind

theorem add_remainder_eq_one (π : _root_.Perm) (h : π.val < 1) :
    π + Perm.remainder π h = 1 := by
  ext
  change π.val + (1 - π.val) = (1 : Rat)
  grind

def diff (π_have π_exhale : _root_.Perm) (h : π_exhale.val < π_have.val) : _root_.Perm :=
  ⟨π_have.val - π_exhale.val, by
    grind⟩

@[simp] theorem diff_val (π_have π_exhale : _root_.Perm) (h : π_exhale.val < π_have.val) :
    (Perm.diff π_have π_exhale h).val = π_have.val - π_exhale.val := rfl

theorem diff_isValid (π_have π_exhale : _root_.Perm)
    (h : π_exhale.val < π_have.val) (hv_have : π_have.IsValid) :
    (Perm.diff π_have π_exhale h).IsValid := by
  show π_have.val - π_exhale.val ≤ 1
  unfold _root_.Perm.IsValid at hv_have
  have : π_have.val ≤ 1 := hv_have
  grind

theorem add_diff_eq_have (π_have π_exhale : _root_.Perm) (h : π_exhale.val < π_have.val) :
    π_exhale + Perm.diff π_have π_exhale h = π_have := by
  ext
  change π_exhale.val + (π_have.val - π_exhale.val) = π_have.val
  grind

end Perm

namespace HeapM

theorem triple_exhale_full {P : hProp} {rest : HeapM α} {Q : α → hProp}
    (x : Loc) (v : Val)
    (hpre : P = x ↦ v)
    (h : ⦃ ∅ ⦄ rest ⦃ Q ⦄) :
    ⦃ P ⦄ (do HeapM.exhale (x ↦[1] v); rest) ⦃ Q ⦄ := by
  apply HeapM.triple_exhale (R := ∅)
  · rw [hpre, hSingle_eq_hSingleFrac]
    rw [hStar_empty]
  · exact h

theorem triple_exhale_frac_lt_one
    {P : hProp} {rest : HeapM α} {Q : α → hProp}
    (x : Loc) (v : Val) (π_exhale : _root_.Perm)
    (hlt : π_exhale.val < 1)
    (hv_exhale : π_exhale.IsValid)
    (hpre : P = x ↦ v)
    (h : ⦃ x ↦[Perm.remainder π_exhale hlt] v ⦄ rest ⦃ Q ⦄) :
    ⦃ P ⦄ (do HeapM.exhale (x ↦[π_exhale] v); rest) ⦃ Q ⦄ := by
  apply HeapM.triple_exhale_frac
    x v π_exhale (Perm.remainder π_exhale hlt)
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
  apply HeapM.triple_exhale_frac_of_frac
    x v π_have π_exhale (Perm.diff π_have π_exhale hlt)
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
    throwError "symexec: cannot parse precondition component: {e}"
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
    throwError "symexec: cannot parse precondition component: {e}"

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

partial def symexecCore : TacticM Unit := do
  logInfo m!"[symexec] Starting symbolic execution"
  symexecLoop
where
  symexecLoop : TacticM Unit := do
    let goal ← getMainGoal
    let goalType ← goal.getType
    let goalType ← instantiateMVars goalType

    logInfo m!"[symexec] ──────────────────────────────"
    logInfo m!"[symexec] Current goal: {goalType}"

    let fn := goalType.getAppFn
    unless fn.isConst && fn.constName! == ``Loom.Triple do
      logInfo m!"[symexec] Goal is not a Triple (fn = {fn}), stopping."
      return

    let args := goalType.getAppArgs
    let numArgs := args.size
    logInfo m!"[symexec] Triple has {numArgs} args"

    let pre := args[numArgs - 4]!
    let code := args[numArgs - 3]!
    let post := args[numArgs - 2]!
    let code ← whnfR code

    logInfo m!"[symexec] Pre:  {pre}"
    logInfo m!"[symexec] Code: {code}"
    logInfo m!"[symexec] Post: {post}"

    if code.isAppOfArity ``Bind.bind 6 then
      let m1 := code.getArg! 4
      let m1 ← whnfR m1
      logInfo m!"[symexec] Code is bind, first command: {m1}"

      if m1.isAppOfArity ``HeapM.inhale 1 then
        let prop := m1.getArg! 0
        logInfo m!"[symexec] ▶ INHALE: {prop}"
        logInfo m!"[symexec]   Applying HeapM.triple_inhale..."
        evalTactic (← `(tactic| apply HeapM.triple_inhale))
        logInfo m!"[symexec]   triple_inhale applied OK"

        logInfo m!"[symexec]   Trying to simplify precondition..."
        trySimplifyPre
        logInfo m!"[symexec]   Precondition simplification done"

        symexecLoop

      else if m1.isAppOfArity ``HeapM.exhale 1 then
        let prop := m1.getArg! 0
        logInfo m!"[symexec] ▶ EXHALE: {prop}"

        let some exhaleChunk ← parseChunk? prop
          | do
              logInfo m!"[symexec]   ERROR: cannot parse exhale prop: {prop}"
              throwError "symexec: cannot parse exhale argument: {prop}"

        logInfo m!"[symexec]   Exhale chunk: loc={exhaleChunk.loc}, val={exhaleChunk.val}, perm={exhaleChunk.perm}"

        processExhale pre exhaleChunk

        logInfo m!"[symexec]   Exhale processed OK, continuing..."
        symexecLoop

      else
        logInfo m!"[symexec]   ERROR: unsupported command in bind: {m1}"
        throwError "symexec: unsupported command in bind: {m1}"

    else if code.isAppOfArity ``HeapM.skip 0 then
      logInfo m!"[symexec] ▶ SKIP"
      evalTactic (← `(tactic|
        first
        | exact Triple.pure () PartialOrder.rel_refl
        | (apply Triple.pure ()
           simp only [PartialOrder.rel, Loom.Perm.remainder, Loom.Perm.diff]
           grind)))
      logInfo m!"[symexec]   Done ✓"

    else if code.isAppOfArity ``Pure.pure 4 then
      logInfo m!"[symexec] ▶ PURE"
      logInfo m!"[symexec]   Applying Triple.pure () PartialOrder.rel_refl..."
      evalTactic (← `(tactic| exact Triple.pure () PartialOrder.rel_refl))
      logInfo m!"[symexec]   Done ✓"

    else if code.isAppOfArity ``HeapM.inhale 1 then
      let prop := code.getArg! 0
      logInfo m!"[symexec] ▶ TERMINAL INHALE: {prop}"
      evalTactic (← `(tactic| apply HeapM.triple_inhale_done))
      logInfo m!"[symexec]   Done ✓"

    else if code.isAppOfArity ``HeapM.exhale 1 then
      let prop := code.getArg! 0
      logInfo m!"[symexec] ▶ TERMINAL EXHALE: {prop}"

      let some exhaleChunk ← parseChunk? prop
        | do
            logInfo m!"[symexec]   ERROR: cannot parse exhale prop: {prop}"
            throwError "symexec: cannot parse exhale argument: {prop}"

      processExhale pre exhaleChunk
      logInfo m!"[symexec]   Terminal exhale done ✓"

    else
      logInfo m!"[symexec]   ERROR: unsupported terminal command: {code}"
      throwError "symexec: unsupported terminal command: {code}"

  trySimplifyPre : TacticM Unit := do
    try
      evalTactic (← `(tactic| apply HeapM.triple_pre_eq; · simp; rfl))
      logInfo m!"[symexec]   ✓ Simplified with triple_pre_eq + simp + rfl"
    catch e =>
      logInfo m!"[symexec]   (simplification skipped: {e.toMessageData})"

  processExhale (pre : Expr) (exhaleChunk : SChunk) : TacticM Unit := do
    logInfo m!"[symexec]   Processing exhale..."
    logInfo m!"[symexec]   Current precondition expr: {pre}"

    let preChunks ← parsePrecond pre
    logInfo m!"[symexec]   Parsed {preChunks.length} chunks from precondition:"
    for i in [:preChunks.length] do
      let c := preChunks[i]!
      logInfo m!"[symexec]     chunk[{i}]: loc={c.loc}, val={c.val}, perm={c.perm}"

    let some (idx, matchedChunk, _remaining) ← findChunk preChunks exhaleChunk.loc exhaleChunk.val
      | do
          logInfo m!"[symexec]   ERROR: no matching chunk found"
          throwError "symexec: cannot find chunk for exhale"

    logInfo m!"[symexec]   Found matching chunk at index {idx}"
    logInfo m!"[symexec]   Matched chunk perm: {matchedChunk.perm}"
    logInfo m!"[symexec]   Exhale chunk perm:  {exhaleChunk.perm}"

    let preStx ← exprToSyntax' pre

    match matchedChunk.perm, exhaleChunk.perm with
    | none, some exhPerm =>
      logInfo m!"[symexec]   Case: exhale FRACTION from FULL"

      let loc ← exprToSyntax' exhaleChunk.loc
      let val ← exprToSyntax' exhaleChunk.val
      let exhPermStx ← exprToSyntax' exhPerm

      if preChunks.length == 1 then
        logInfo m!"[symexec]   Single chunk. Applying local full→fraction rule..."
        evalTactic (← `(tactic|
          first
          | apply (HeapM.triple_exhale_full (P := $preStx) $loc $val rfl)
          | apply (HeapM.triple_exhale_frac_lt_one (P := $preStx) $loc $val $exhPermStx
              (by
                simp [Loom.Perm.remainder, Loom.Perm.diff, _root_.Perm.IsValid, _root_.Perm.le_def]
                grind)
              (by
                simp [Loom.Perm.remainder, Loom.Perm.diff, _root_.Perm.IsValid, _root_.Perm.le_def]
                grind)
              rfl)))
        logInfo m!"[symexec]   ✓ Exhale (full→frac, single) applied"
      else
        logInfo m!"[symexec]   Multiple chunks ({preChunks.length}). Not yet implemented."
        throwError "symexec: multi-chunk exhale from full not yet implemented"

    | some havePerm, some exhPerm =>
      logInfo m!"[symexec]   Case: exhale FRACTION from FRACTION"

      let loc ← exprToSyntax' exhaleChunk.loc
      let val ← exprToSyntax' exhaleChunk.val
      let havePermStx ← exprToSyntax' havePerm
      let exhPermStx ← exprToSyntax' exhPerm

      if preChunks.length == 1 then
        logInfo m!"[symexec]   Single chunk. Applying local frac→frac rule..."
        evalTactic (← `(tactic|
          apply (HeapM.triple_exhale_frac_of_frac_lt (P := $preStx) $loc $val $havePermStx $exhPermStx
            (by
              simp [Loom.Perm.remainder, Loom.Perm.diff, _root_.Perm.IsValid, _root_.Perm.le_def]
              grind)
            (by
              simp [Loom.Perm.remainder, Loom.Perm.diff, _root_.Perm.IsValid, _root_.Perm.le_def]
              grind)
            (by
              simp [Loom.Perm.remainder, Loom.Perm.diff, _root_.Perm.IsValid, _root_.Perm.le_def]
              grind)
            rfl)))
        logInfo m!"[symexec]   ✓ Exhale (frac→frac, single) applied"
      else
        logInfo m!"[symexec]   Multiple chunks ({preChunks.length}). Not yet implemented."
        throwError "symexec: multi-chunk exhale from frac not yet implemented"

    | none, none =>
      logInfo m!"[symexec]   Case: exhale FULL from FULL. Not yet implemented."
      throwError "symexec: exhale full from full not yet implemented"

    | some _, none =>
      logInfo m!"[symexec]   Case: exhale FULL from FRACTION. Impossible."
      throwError "symexec: cannot exhale full permission from fractional chunk"

    logInfo m!"[symexec]   Skipping post-exhale precondition simplification"

elab "symexec" : tactic => symexecCore


example (p : Loc) (v : Val) :
    ⦃ ∅ ⦄
    (do HeapM.inhale (p ↦ v)
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
