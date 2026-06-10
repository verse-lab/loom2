import Lean
import Loom.Tactic.Intros

open Lean Elab Command Term Meta Order Loom

/-! ## Helpers -/

public def optionalIdentNames (ids : Array (Option Ident)) : Array (Option Name) :=
  ids.map fun
    | some id => some id.getId
    | none => none

public def explicitNames (names : Array Name) : Array (Option Name) :=
  names.map some

/-- Build a right-nested `NamedProp` list.

`names[i] = none` means use the generated name `{pfx}{i+1}`. The generated term
omits the optional syntax argument, so `NamedProp.one`/`cons` use their `none`
default. -/
public def mkNamedPropList (ts : Array (TSyntax `term)) (names : Array (Option Name) := #[])
    (pfx : String := "clause") : MacroM (TSyntax `term) := do
  if ts.isEmpty then
    `(term| True)
  else
    let namedPropOne := mkIdent ``Loom.NamedProp.one
    let namedPropCons := mkIdent ``Loom.NamedProp.cons
    let getName (i : Nat) : MacroM (TSyntax `term) := do
      let name := match names[i]? with
        | some (some name) => name.toString
        | _ => s!"{pfx}{i + 1}"
      let nameStr := Lean.Syntax.mkStrLit name
      `(Lean.Name.mkSimple $nameStr)
    let lastIdx := ts.size - 1
    let mut result ← `($namedPropOne ($(← getName lastIdx)) $(ts[lastIdx]!))
    for i in List.range lastIdx |>.reverse do
      result ← `($namedPropCons ($(← getName i)) $(ts[i]!) $result)
    return result
