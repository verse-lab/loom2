import Loom.Test.Velvet.Syntax
open Velvet

-- Test the ⸨ ⸩ notation
#check (⸨ True ⸩ (pure 42 : Option Nat) ⸨ r, r = 42 ⸩ : Prop)
#check (⸨ True ⸩ (pure 42 : Option Nat) ⸨ fun r => r = 42 ⸩ : Prop)

-- Test in a theorem statement
example : ⸨ True ⸩ (pure 42 : Option Nat) ⸨ r, r = 42 ⸩ := by
  apply Std.Do'.Triple.intro; intro _; rfl
