import Lean
import Loom.Tactic.Intros

open Lean Elab Command Term Meta Order Loom

/-! ## Helpers -/

/-- Fold invariants into an `InvListWithNames` — a named conjunction list. -/
public def foldInvariants (invs : Array (Lean.TSyntax `term))
    (names : Array (Option Ident) := #[]) : Lean.MacroM (Lean.TSyntax `term) := do
  if invs.isEmpty then `(True)
  else
    let invListOne := mkIdent ``Loom.InvListWithNames.one
    let invListCons := mkIdent ``Loom.InvListWithNames.cons
    -- Build right-nested InvListWithNames: cons h₁ inv₁ (cons h₂ inv₂ (one h₃ inv₃))
    let getName (i : Nat) : Lean.MacroM (Lean.TSyntax `term) := do
      let name := match names[i]? with
        | some (some id) => id.getId.toString
        | _ => s!"invariant{i + 1}"
      let nameStr := Lean.Syntax.mkStrLit name
      `(Lean.Name.mkSimple $nameStr)
    let lastIdx := invs.size - 1
    let mut result ← `($invListOne ($(← getName lastIdx)) $(invs[lastIdx]!))
    for i in List.range lastIdx |>.reverse do
      result ← `($invListCons ($(← getName i)) $(invs[i]!) $result)
    return result


/-- Fold terms into an `InvListWithNames` — a named conjunction list. -/
public def andList (ts : Array (TSyntax `term)) (names : Array Name := #[])
    (pfx : String := "clause") : MacroM (TSyntax `term) := do
  if ts.size = 0 then `(term| True) else
    let invListOne := mkIdent ``Loom.InvListWithNames.one
    let invListCons := mkIdent ``Loom.InvListWithNames.cons
    let getName (i : Nat) : MacroM (TSyntax `term) := do
      let name := if i < names.size then names[i]!.toString else s!"{pfx}{i + 1}"
      let nameStr := Lean.Syntax.mkStrLit name
      `(Lean.Name.mkSimple $nameStr)
    let lastIdx := ts.size - 1
    let mut result ← `($invListOne ($(← getName lastIdx)) $(ts[lastIdx]!))
    for i in List.range lastIdx |>.reverse do
      result ← `($invListCons ($(← getName i)) $(ts[i]!) $result)
    return result
