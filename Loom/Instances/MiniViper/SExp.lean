import Loom.Instances.MiniViper.Values


inductive SExp where
  | sLit : Val → SExp
  | sVar : Nat → SExp
  | sUnop : Unop → SExp → SExp
  | sBinop : SExp → Binop → SExp → SExp
  | sHasType : VTyp → Nat → SExp
  | sBinopSafe : SExp → Binop → SExp → SExp
  deriving Repr, BEq

namespace SExp


abbrev sBool (b : Bool) := sLit (.vBool b)
abbrev sInt (n : Int) := sLit (.vInt n)
abbrev sPerm (p : Rat) := sLit (.vPerm p)
abbrev sNull := sLit (.vRef .null)

def sNot (t : SExp) : SExp := sUnop .not t
def sAnd (t1 t2 : SExp) : SExp := sBinop t1 .and t2
def sEq (t1 t2 : SExp) : SExp := sBinop t1 .eq t2
def sNeq (t1 t2 : SExp) : SExp := sBinop t1 .neq t2
def sLt (t1 t2 : SExp) : SExp := sBinop t1 .lt t2
def sLte (t1 t2 : SExp) : SExp := sBinop t1 .lte t2
def sImp (t1 t2 : SExp) : SExp := sBinop t1 .imp t2
def sSub (t1 t2 : SExp) : SExp := sBinop t1 .sub t2
def sAdd (t1 t2 : SExp) : SExp := sBinop t1 .add t2
def sPermDiv (t1 t2 : SExp) : SExp := sBinop t1 .permDiv t2


def eval (e : SExp) (V : Nat → Option Val) : Option Val :=
  match e with
  | .sLit v => some v
  | .sVar n => V n
  | .sUnop op t =>
    (eval t V).bind (evalUnop op ·)
  | .sBinop t1 op t2 =>
    (eval t1 V).bind fun v1 =>
    (eval t2 V).bind fun v2 =>
    (evalBinop v1 op v2).toOption
  | .sHasType ty n =>
    (V n).bind fun v =>
    if valMatchesType v ty then some (.vBool true) else none
  | .sBinopSafe t1 op t2 =>
    (eval t1 V).bind fun v1 =>
    (eval t2 V).bind fun v2 =>
    match evalBinop v1 op v2 with
    | .opFailure => none
    | _ => some (.vBool true)

def isGround : SExp → Bool
  | .sLit _ => true
  | .sVar _ => false
  | .sUnop _ t => isGround t
  | .sBinop t1 _ t2 => isGround t1 && isGround t2
  | .sHasType _ _ => false
  | .sBinopSafe t1 _ t2 => isGround t1 && isGround t2


def evalGround (e : SExp) : Option Val :=
  eval e (fun _ => none)

def collectConjuncts : SExp → List SExp
  | .sBinop t1 .and t2 => collectConjuncts t1 ++ collectConjuncts t2
  | t => [t]

private def triviallyTrue : SExp → Bool
  | .sLit (.vBool true) => true
  | .sBinop t1 .eq t2 => t1 == t2
  | .sUnop .not (.sBinop (.sLit v1) .eq (.sLit v2)) => v1 != v2
  | .sBinop t1 .and t2 => triviallyTrue t1 && triviallyTrue t2
  | e => if e.isGround then
      match e.evalGround with
      | some (.vBool true) => true
      | _ => false
    else false

end SExp


private def diseqForms (t : SExp) : List SExp :=
  match t with
  | .sUnop .not (.sBinop a .eq b) =>
    [t, SExp.sBinop a .neq b, SExp.sUnop .not (SExp.sBinop b .eq a), SExp.sBinop b .neq a]
  | .sBinop a .neq b =>
    [t, SExp.sUnop .not (SExp.sBinop a .eq b), SExp.sBinop b .neq a, SExp.sUnop .not (SExp.sBinop b .eq a)]
  | _ => [t]


def symImplies (pc t : SExp) : Bool :=
  if t.triviallyTrue then true
  else match t with
  | .sBinopSafe _ op _ => binopAlwaysSafe op
  | _ =>
    let conjuncts := pc.collectConjuncts
    let forms := diseqForms t
    forms.any fun f => conjuncts.any (· == f)
