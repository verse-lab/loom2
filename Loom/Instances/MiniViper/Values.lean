abbrev FieldName := String
abbrev Address := Nat

inductive Ref where
  | address : Address → Ref
  | null : Ref
  deriving DecidableEq, Repr, BEq

inductive Val where
  | vBool : Bool → Val
  | vInt : Int → Val
  | vPerm : Rat → Val
  | vRef : Ref → Val
  deriving DecidableEq, Repr, BEq

inductive Lit where
  | lBool : Bool → Lit
  | lInt : Int → Lit
  | lPerm : Rat → Lit
  | lNull : Lit
  deriving DecidableEq, Repr, BEq

def valOfLit : Lit → Val
  | .lBool b => .vBool b
  | .lInt n => .vInt n
  | .lPerm p => .vPerm p
  | .lNull => .vRef .null

inductive VTyp where
  | tBool | tInt | tPerm | tRef
  deriving DecidableEq, Repr, BEq

inductive Binop where
  | and | or | imp
  | eq | neq
  | lt | lte
  | add | sub
  | permDiv
  deriving DecidableEq, Repr, BEq

inductive Unop where
  | not | neg
  deriving DecidableEq, Repr, BEq

inductive BinopResult where
  | normal : Val → BinopResult
  | opFailure : BinopResult
  | typeFailure : BinopResult
  deriving DecidableEq, Repr

def BinopResult.toOption : BinopResult → Option Val
  | .normal v => some v
  | _ => none

def evalBinop (v1 : Val) (op : Binop) (v2 : Val) : BinopResult :=
  match op, v1, v2 with
  | .and, .vBool b1, .vBool b2 => .normal (.vBool (b1 && b2))
  | .or, .vBool b1, .vBool b2 => .normal (.vBool (b1 || b2))
  | .imp, .vBool b1, .vBool b2 => .normal (.vBool (!b1 || b2))
  | .eq, _, _ => .normal (.vBool (v1 == v2))
  | .neq, _, _ => .normal (.vBool (v1 != v2))
  | .lt, .vInt n1, .vInt n2 => .normal (.vBool (decide (n1 < n2)))
  | .lte, .vInt n1, .vInt n2 => .normal (.vBool (decide (n1 ≤ n2)))
  | .lt, .vPerm p1, .vPerm p2 => .normal (.vBool (decide (p1 < p2)))
  | .lte, .vPerm p1, .vPerm p2 => .normal (.vBool (decide (p1 ≤ p2)))
  | .add, .vInt n1, .vInt n2 => .normal (.vInt (n1 + n2))
  | .sub, .vInt n1, .vInt n2 => .normal (.vInt (n1 - n2))
  | .add, .vPerm p1, .vPerm p2 => .normal (.vPerm (p1 + p2))
  | .sub, .vPerm p1, .vPerm p2 => .normal (.vPerm (p1 - p2))
  | .permDiv, .vPerm p1, .vPerm p2 =>
    if p2 == 0 then .opFailure else .normal (.vPerm (p1 / p2))
  | .permDiv, .vPerm p1, .vInt n2 =>
    if n2 == 0 then .opFailure else .normal (.vPerm (p1 / (↑n2 : Rat)))
  | _, _, _ => .typeFailure

def evalUnop (op : Unop) (v : Val) : Option Val :=
  match op, v with
  | .not, .vBool b => some (.vBool (!b))
  | .neg, .vInt n => some (.vInt (-n))
  | _, _ => none

/-- Lazy boolean: returns (shortCircuitValue, result) if first operand determines result -/
def binopLazyBool : Binop → Option (Bool × Bool)
  | .or => some (true, true)
  | .and => some (false, false)
  | .imp => some (false, true)
  | _ => none

/-- Operations that never produce BinopOpFailure -/
def binopAlwaysSafe : Binop → Bool
  | .eq | .neq | .and | .or | .imp | .lt | .lte | .add | .sub => true
  | _ => false

def valMatchesType : Val → VTyp → Bool
  | .vBool _, .tBool => true
  | .vInt _, .tInt => true
  | .vPerm _, .tPerm => true
  | .vRef _, .tRef => true
  | _, _ => false
