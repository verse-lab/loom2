import Loom.Test.Velvet.Syntax

attribute [-grind] getElem?_neg getElem?_pos getElem!_neg getElem!_pos

@[grind]
def IntIsEven (n : Int) : Prop := n % 2 = 0

method isEven (n : Int)
  return (result : Bool)
  ensures result = true ↔ IntIsEven n
  do
  if n % 2 = 0 then
    return true
  else
    return false

set_option maxHeartbeats 10000000

prove_correct isEven by
  mvcgen' simplifying_assumptions with grind
