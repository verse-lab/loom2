import Lean

/-!
Marker operations used by Velvet loop syntax.

They erase computationally to `pure ⟨⟩`, but their arguments remain visible to
the WP/spec machinery before unfolding.
-/

set_option linter.unusedVariables false in
def invariantGadget {m : Type u → Type v} [Monad m] (inv : Prop) : m PUnit := pure ⟨⟩

set_option linter.unusedVariables false in
def decreasingGadget {m : Type u → Type v} [Monad m] (measure : Nat) : m PUnit := pure ⟨⟩

set_option linter.unusedVariables false in
def onDoneGadget {m : Type u → Type v} [Monad m] (done : Prop) : m PUnit := pure ⟨⟩
