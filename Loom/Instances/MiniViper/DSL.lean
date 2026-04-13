import Loom.Instances.MiniViper.SymExec

open SExp Stmt Assert AtomicAssert PureExp PermExp Lit Binop

namespace DSL

syntax "x![" num "]" : term
macro_rules
  | `(x![$n:num]) => `(PureExp.var $n)

syntax "i![" num "]" : term
macro_rules
  | `(i![$n:num]) => `(PureExp.eLit (Lit.lInt $n))

syntax "p![" num "]" : term
syntax "p![" num "/" num "]" : term
macro_rules
  | `(p![$n:num]) => `(PureExp.eLit (Lit.lPerm $n))
  | `(p![$a:num / $b:num]) => `(PureExp.eLit (Lit.lPerm ($a / $b)))

syntax "b!true" : term
syntax "b!false" : term
macro_rules
  | `(b!true)  => `(PureExp.eLit (Lit.lBool true))
  | `(b!false) => `(PureExp.eLit (Lit.lBool false))

syntax "null!" : term
macro_rules
  | `(null!) => `(PureExp.eLit Lit.lNull)

syntax:65 (name := peq) term " == " term : term
syntax:65 (name := pne) term " != " term : term
syntax:65 (name := plt) term " < "  term : term
syntax:65 (name := ple) term " <= " term : term
syntax:70 (name := padd) term " + "  term : term
syntax:70 (name := psub) term " - "  term : term

macro_rules (kind := peq)
  | `($x == $y) => `(PureExp.binop $x Binop.eq $y)

macro_rules (kind := pne)
  | `($x != $y) => `(PureExp.binop $x Binop.neq $y)

macro_rules (kind := plt)
  | `($x < $y) => `(PureExp.binop $x Binop.lt $y)

macro_rules (kind := ple)
  | `($x <= $y) => `(PureExp.binop $x Binop.lte $y)

macro_rules (kind := padd)
  | `($x + $y) => `(PureExp.binop $x Binop.add $y)

macro_rules (kind := psub)
  | `($x - $y) => `(PureExp.binop $x Binop.sub $y)

syntax "fld(" term ", " str ")" : term
macro_rules
  | `(fld($recv, $f:str)) => `(PureExp.fieldAcc $recv $f)

syntax "pure{" term "}" : term
macro_rules
  | `(pure{$p}) => `(Assert.atomic (AtomicAssert.pure $p))

syntax "acc(" term ", " str ", " term ")" : term
macro_rules
  | `(acc($recv, $f:str, $perm)) =>
      `(Assert.atomic (AtomicAssert.acc $recv $f (PermExp.pureExp $perm)))

syntax "acc*(" term ", " str ")" : term
macro_rules
  | `(acc*($recv, $f:str)) =>
      `(Assert.atomic (AtomicAssert.acc $recv $f PermExp.wildcard))

infixr:61 " ** " => Assert.star

syntax "inhale! " term : term
syntax "exhale! " term : term
macro_rules
  | `(inhale! $a) => `(Stmt.inhale $a)
  | `(exhale! $a) => `(Stmt.exhale $a)

syntax "do!" "[" term,* "]" : term
macro_rules
  | `(do![ $s:term ]) => `($s)
  | `(do![ $s:term, $rest:term,* ]) =>
      `(Stmt.seq $s (do![ $rest,* ]))

end DSL
