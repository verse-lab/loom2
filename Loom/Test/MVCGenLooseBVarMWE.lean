import Lean
import Loom.Test.Specs
import Loom.Tactic.VCGen

open Loom Lean Meta Order

/-
Minimal repro for the current `mvcgen'` regression on the
`joachim/instantiateMVarsNoUpdate`-based Lean build.

Expected: `mvcgen'` should reduce the WP for `get; set`.
Actual: it produces a malformed intermediate goal containing a loose de Bruijn
index (`wp (set #0) ...`), and the tactic fails with `unknown goal` / kernel
errors.
-/
example (s : Nat) :
    wp (do
      let x <- get (m := StateM Nat)
      set x)
      (fun _ s' => s = s')
      ⟨⟩
      s := by
  mvcgen'
