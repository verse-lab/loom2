/-
Minimal reproducer: Sym.simpGoal crashes on kernel projections (Expr.proj).

The issue: `Sym.Simp.simpStep` throws on `Expr.proj` nodes, expecting them to
be folded into application form beforehand. But `Sym.simpGoal` does not call
`foldProjs`, unlike `Grind.preprocess` which does (Grind/Simp.lean:66).
-/
import Lean

open Lean Meta Elab Tactic

/-- Tactic that calls `Sym.simpGoal` on the current goal. -/
elab "sym_simp" : tactic => do
  let goal ← getMainGoal
  let r ← Sym.SymM.run <| Sym.simpGoal goal
  match r with
  | .closed => replaceMainGoal []
  | .goal g => replaceMainGoal [g]
  | .noProgress => pure ()

/-- Replace `Prod.fst`/`Prod.snd` applications with definitionally equal
    kernel projections (`Expr.proj`). This simulates what happens when
    Lean's unifier or reduction engine produces projection terms. -/
elab "to_kernel_proj" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let target' ← Meta.transform target (post := fun e => do
      match e.getAppFn.constName?, e.getAppNumArgs with
      | some ``Prod.snd, 3 => return .done (mkProj ``Prod 1 e.appArg!)
      | some ``Prod.fst, 3 => return .done (mkProj ``Prod 0 e.appArg!)
      | _, _ => return .continue)
    let g ← goal.replaceTargetDefEq target'
    replaceMainGoal [g]

-- `to_kernel_proj` converts `p.snd` (Prod.snd p) into `Expr.proj Prod 1 p`,
-- which is definitionally equal but in kernel representation.
-- `sym_simp` then crashes because Sym.Simp doesn't handle Expr.proj.

/--
error: unexpected kernel projection term during simplification
  p.2
pre-process and fold them as projection applications
-/
#guard_msgs in
example (p : Nat × Nat) : p.2 + 1 > 0 := by
  to_kernel_proj
  sym_simp
  omega
