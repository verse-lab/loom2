import Loom.Test.Velvet.Syntax
import Loom.Tactic.Intros

-- Check what WithHypName looks like in an Expr
#check @Loom.WithHypName
#check Loom.WithHypName (1 = 1) (Lean.Name.mkSimple "test")
open Lean in
#eval do
  let e := mkApp3 (mkConst ``Loom.WithHypName) (mkApp2 (mkConst ``Eq [1]) (mkConst ``Nat) (mkNatLit 1)) (mkConst ``Lean.Name.anonymous) (mkConst ``Lean.Name.anonymous)
  IO.println s!"isApp3: {e.isAppOfArity ``Loom.WithHypName 3}"
