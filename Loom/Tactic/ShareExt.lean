import Lean

open Lean Parser Meta Elab Tactic Sym Lean.Order

open Sym Sym.Internal

-- The following function is vendored until it is made public:
/-- `mkAppRevRangeS f b e args == mkAppRev f (revArgs.extract b e)` -/
meta def mkAppRevRangeS [Monad m] [Internal.MonadShareCommon m] (f : Expr) (beginIdx endIdx : Nat) (revArgs : Array Expr) : m Expr :=
  loop revArgs beginIdx f endIdx
where
  loop (revArgs : Array Expr) (start : Nat) (b : Expr) (i : Nat) : m Expr := do
  if i ≤ start then
    return b
  else
    let i := i - 1
    loop revArgs start (← mkAppS b revArgs[i]!) i


meta def mkAppRevS [Monad m] [Internal.MonadShareCommon m] (f : Expr) (revArgs : Array Expr) : m Expr :=
  mkAppRevRangeS f 0 revArgs.size revArgs


meta def mkAppRangeS [Monad m] [Internal.MonadShareCommon m] (f : Expr) (beginIdx endIdx : Nat) (args : Array Expr) : m Expr :=
  loop args endIdx f beginIdx
where
  loop (args : Array Expr) (end' : Nat) (b : Expr) (i : Nat) : m Expr := do
  if end' ≤ i then
    return b
  else
    loop args end' (← mkAppS b args[i]!) (i + 1)

meta def mkAppNS [Monad m] [Internal.MonadShareCommon m] (f : Expr) (args : Array Expr) : m Expr :=
  mkAppRangeS f 0 args.size args


meta def mkAppS₆ [Monad m] [Internal.MonadShareCommon m] (f a₁ a₂ a₃ a₄ a₅ a₆ : Expr) : m Expr := do
  mkAppS (← mkAppS₅ f a₁ a₂ a₃ a₄ a₅) a₆

meta def mkAppS₇ [Monad m] [Internal.MonadShareCommon m] (f a₁ a₂ a₃ a₄ a₅ a₆ a₇ : Expr) : m Expr := do
  mkAppS (← mkAppS₆ f a₁ a₂ a₃ a₄ a₅ a₆) a₇

meta def mkAppS₈ [Monad m] [Internal.MonadShareCommon m] (f a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ : Expr) : m Expr := do
  mkAppS (← mkAppS₇ f a₁ a₂ a₃ a₄ a₅ a₆ a₇) a₈

meta def mkAppS₉ [Monad m] [Internal.MonadShareCommon m] (f a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ : Expr) : m Expr := do
  mkAppS (← mkAppS₈ f a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈) a₉
