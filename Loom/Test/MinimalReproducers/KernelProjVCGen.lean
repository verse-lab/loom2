/-
Minimal reproducer: kernel projections (`Expr.proj`) arising inside `mvcgen'`.

Root cause chain:
1. Method has ≥3 mutable variables → `do` packs them into nested
   `MProd Nat (MProd (Array Nat) (Array Nat))`
2. The `Pure.pure` backward rule application (`Lean.Meta.apply`) unifies
   the postcondition with the loop state. The unifier normalizes
   `MProd.snd (MProd.snd s)` into kernel `Expr.proj` nodes (`.2.snd`).
   (`Bind.bind` and `ForIn.forIn` specs also introduce projections,
   but only `Pure.pure`'s result triggers the crash.)
3. The `∀ x, ...` postcondition is not a lattice connective (`meet`/`himp`/`pure`),
   so `classifyGoalKind` returns `.Unknown`
4. The `.Unknown` handler calls `Sym.simpGoal` on the target containing `.2`
5. `Sym.Simp.simpStep` throws because it doesn't handle `Expr.proj`

VCGen works around this via `Grind.foldProjs` (VCGen.lean:284).
Comment it out to see the crash.
-/
import Loom.Test.Velvet.Syntax

@[grind] def isOdd (x : Nat) : Bool := x % 2 = 1

method minRepr (arr : Array Nat)
  return (result : Array Nat)
  ensures ∀ x, isOdd x = false → result.count x = 0
  do
  let mut result : Array Nat := #[]
  let mut idx : Array Nat := #[]
  let mut i : Nat := 0
  while' i < arr.size
    invariant i ≤ arr.size
    invariant idx.size = result.size
    invariant ∀ x, isOdd x = false → result.count x = 0
  do
    if isOdd arr[i]! = true then
      result := result.push arr[i]!
      idx := idx.push i
    i := i + 1
  return result

prove_correct minRepr by
  mvcgen' simplifying_assumptions with grind
