import Loom.Instances.MiniViper.Values

inductive PureExp where
  | eLit : Lit → PureExp
  | var : Nat → PureExp
  | unop : Unop → PureExp → PureExp
  | binop : PureExp → Binop → PureExp → PureExp
  | condExp : PureExp → PureExp → PureExp → PureExp
  | fieldAcc : PureExp → FieldName → PureExp
  deriving Repr

inductive PermExp where
  | pureExp : PureExp → PermExp
  | wildcard : PermExp
  deriving Repr

inductive AtomicAssert where
  | pure : PureExp → AtomicAssert
  | acc : PureExp → FieldName → PermExp → AtomicAssert
  deriving Repr

inductive Assert where
  | atomic : AtomicAssert → Assert
  | imp : PureExp → Assert → Assert
  | condAssert : PureExp → Assert → Assert → Assert
  | star : Assert → Assert → Assert
  deriving Repr

inductive Stmt where
  | skip : Stmt
  | inhale : Assert → Stmt
  | exhale : Assert → Stmt
  | seq : Stmt → Stmt → Stmt
  | ite : PureExp → Stmt → Stmt → Stmt
  | localAssign : Nat → PureExp → Stmt
  | havoc : Nat → Stmt
  | fieldAssign : PureExp → FieldName → PureExp → Stmt
  deriving Repr
