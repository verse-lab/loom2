import Loom.Test.Velvet.Syntax

method_fix gcd (a : Nat) (b : Nat) return (res : Nat)
  ensures h : res = Nat.gcd a b
  do
    if b = 0 then return a
    else
      let r ← gcd b (a % b)
      return r

set_option maxHeartbeats 800000

prove_correct gcd by
  mvcgen' simplifying_assumptions with grind
  all_goals grind [Nat.gcd_comm, Nat.gcd_rec]
