import Loom.Triple.Basic
import Loom.Frame

open Lean Order

namespace Loom

universe u v
variable {m : Type u → Type v} {l : Type u} {e : Type u} [Monad m] [WPMonad m l e]

variable [Monad m] [WPMonad m l e] in
set_option linter.unusedVariables false in
def assertGadget (name : Name) (as : l) : m PUnit := pure ⟨⟩

theorem Spec.assertGadget (name : Name) (as : l) [Frame l] :
  Triple (m := m) (as ⊓ (as ⇨ post ⟨⟩)) (Loom.assertGadget name as) post epost := by
  simpa [Loom.assertGadget] using
    (Triple.pure (m := m) (pre := as ⊓ himp as (post ⟨⟩)) (post := post) (epost := epost)
      (a := ⟨⟩) (h := himp_sound (a := as) (b := post ⟨⟩)))

end Loom
