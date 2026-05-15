import Loom.Triple.Basic
import Loom.Tactic.VCGen

namespace Std.Do

#print WPMonad

instance : WPMonad Id.{u} PostShape.pure.{u} where
  wp_pure a := by simp [wp]
  wp_bind x f := by simp [wp]

#check Assertion

example : Assertion (.pure) = ULift Prop := rfl

opaque foo : Id Nat

example : Triple foo ⌜True⌝ (PostCond.noThrow fun _ => ⌜True⌝) := by sorry

end Std.Do

namespace Std.Do'

open Lean.Order

instance : WP Id.{u} Prop EPost⟨⟩ where
  wpTrans x := ⟨fun post _epost => post x⟩
  wp_trans_pure _x := PartialOrder.rel_refl
  wp_trans_bind _x _f := PartialOrder.rel_refl
  wp_trans_monotone x := fun _ _ _ _ _ hpost => hpost x

opaque foo : Id Nat

example : Triple True foo (fun _ => True) epost⟨⟩ := by sorry


end Std.Do'
