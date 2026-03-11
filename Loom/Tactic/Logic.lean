import Lean
import Loom.Tactic.Attr
import Loom.Tactic.ShareExt
import Loom.WP.SimpLemmas
import Loom.Frame

open Lean Meta Sym Loom Lean.Order

namespace Loom

inductive LogicOp where
  | And
  | Imp
  -- Temporarily disabled:
  -- | Forall (n : Name)

/-- Map lattice connective declaration names to supported `LogicOp`s. -/
def _root_.Lean.Name.toLogicOp? : Name → Option LogicOp
  | ``meet => some .And
  | ``himp => some .Imp
  | _ => none

def LogicOp.mkLatticeExpr (as : Array Expr) : LogicOp → MetaM Expr
  | .And => mkAppM ``meet as
  | .Imp => mkAppM ``himp as

/-- Map a logic operator to its corresponding `*_fun_apply` lemma. -/
def LogicOp.toApplyLemma : LogicOp → Name
  | .And => ``meet_fun_apply
  | .Imp => ``himp_fun_apply

/-- Map a logic operator to its corresponding proposition-level equivalence lemma. -/
def LogicOp.toPropLemma : LogicOp → Name
  | .And => ``meet_prop_eq_and
  | .Imp => ``himp_prop_eq_imp

/-- Lift an equality `lhs = rhs` to `(lhs args...) = (rhs args...)`. -/
private def liftEqByArgs (eqPrf : Expr) (args : List Expr) : MetaM Expr := do
  if args.isEmpty then
    return eqPrf
  let eqTy ← inferType eqPrf
  let some (_, lhs, _rhs) := eqTy.eq?
    | throwError "Expected equality proof, got {indentExpr eqTy}"
  let lhsTy ← inferType lhs
  let context ← withLocalDecl `x .default lhsTy fun x => do
    let app := mkAppN x args.toArray
    mkLambdaFVars #[x] app
  mkCongrArg context eqPrf

/--
Apply a function-extensional lemma (`*_fun_apply`) repeatedly over all excess
arguments, producing an equality at the fully applied level.

Example (`lop = .And`, `stepThm = ``meet_fun_apply`, `as = #[a, b]`,
`ss = [s₁, s₂]`): the resulting proof has type
`((a ⊓ b) s₁ s₂) = (a s₁ s₂ ⊓ b s₁ s₂)`.
-/
partial def LogicOp.mkApplyEq
    (stepThm : Name) (lop : LogicOp)
    (as : Array Expr) (ss : List Expr) : MetaM Expr := do
  match ss with
  | [] => mkEqRefl =<< lop.mkLatticeExpr as
  | s :: ss' =>
    let step ← mkAppM stepThm <| as.push s
    if ss'.isEmpty then
      return step
    let stepLift ← liftEqByArgs step ss'
    let as := as.map (mkApp · s)
    let rest ← lop.mkApplyEq stepThm as ss'
    mkEqTrans stepLift rest

/-- Compute binder names/types used for fresh metavariables for logic operands. -/
def mkArgNamesTypes (as : Array Expr) : SymM (Array (Name × Expr)) := do
  as.mapM fun arg => return (`s, ← Sym.inferType arg)

/--
Build:
1) `goal`: lattice expression applied to excess args,
2) `premise`: the corresponding proposition-level formula,
3) `eq`: proof `goal = premise`.
-/
def LogicOp.mkGoalPremiseEq
    (lop : LogicOp) (as ss : Array Expr) : SymM (Expr × Expr × Expr) := do
  let applyLemma := lop.toApplyLemma
  let propLemma := lop.toPropLemma
  let lat ← lop.mkLatticeExpr as
  -- This is the final lattice-side goal `a ⊓ b s₁ ... sₙ` after applying excess state args.
  let goal ← mkAppNS lat ss
  -- Equality rewriting the lattice connective under all excess applications.
  let eqFun ← lop.mkApplyEq applyLemma as ss.toList
  -- Apply all excess args to each operand (`a s₁ .. sₙ`, `b s₁ .. sₙ`).
  let asApp := as.map (mkAppN · ss)
  -- Instantiate the proposition-level equivalence `a s₁ ... sₙ ⊓ b s₁ ... sₙ = a ∧ b s₁ ... sₙ` theorem for applied operands.
  let eqProp ← mkAppM propLemma asApp
  -- Extract the proposition-side RHS from the equality type: `a s₁ ... sₙ ⊓ b s₁ ... sₙ`
  let eqTy ← Sym.inferType eqProp
  let some (_, _lhsProp, rhsProp) := eqTy.eq?
    | throwError "Expected equality from {propLemma}, got {indentExpr eqTy}"
  -- Chain function-application rewriting with proposition equivalence.
  let eq ← mkEqTrans eqFun eqProp
  -- Return lattice goal, logical premise, and bridge equality.
  return (goal, rhsProp, eq)

/--
  Creates a reusable backward rule for a `CompleteLattice` logic expression.
  For example, if `lop` is `And`, then it creates a following theorem for fixed Complete Lattice `l` and
  its `[CompleteLattice l]` instance expression:

  ```
  -- `l` and `[CompleteLattice l]` are fixed
  theorem And_applied_intro (a : l) (b : l) s₁ : σ₁) (s₂ : σ₂) ... (sₙ : σₙ) :
    a s₁ ... sₙ ∧ b s₁ ... sₙ ->
    (a ⊓ b) s₁ ... sₙ
  ```
-/
def LogicOp.mkBackwardRuleForLogic (lop : LogicOp) (as : Array Expr) (excessArgs : Array Expr) : SymM BackwardRule := do

  -- Fresh metavariables become universally quantified after `abstractMVars`.
  let as ← as.mapM fun arg => do
    mkFreshExprMVar (userName := `a) (← Sym.inferType arg)
  let ss ← excessArgs.mapM fun arg => do
    mkFreshExprMVar (userName := `s) (← Sym.inferType arg)

  -- Build premise/goal bridge and turn it into `premise → goal`.
  let (goal, premise, eqGoalPremise) ← lop.mkGoalPremiseEq as ss
  let eqSymm ← mkEqSymm eqGoalPremise
  let prf ← mkAppM ``Eq.mp #[eqSymm]
  let prf ← mkExpectedTypeHint prf (← mkArrow premise goal)

  -- Abstract mvars, create an auxiliary declaration, and package as backward rule.
  let res ← abstractMVars prf
  let type ← preprocessExpr (← Meta.inferType res.expr)
  let prf ← Meta.mkAuxLemma res.paramNames.toList type res.expr
  mkBackwardRuleFromDecl prf

private def withNameHead? (e : Expr) : Option (Array Expr) :=
  let e := e.consumeMData
  if e.isAppOf ``withName then
    some e.getAppArgs
  else
    none

private def evalNameExpr? (e : Expr) : MetaM (Option Name) := do
  try
    return some (← Lean.Meta.reduceEval e)
  catch _ =>
    return none

/--
Introduce exactly one binder. If the binder domain is of shape `withName n x`,
introduce it using name `n`; otherwise fall back to regular `introN 1`.
-/
def intro1WithName (mvarId : MVarId) : SymM IntrosResult := do
  let type ← mvarId.getType
  let .forallE info domain tp body := type | return .failed
  let some args := withNameHead? domain
    | introN mvarId 1
  if h : args.size > 2 then
    let some n ← evalNameExpr? args[0]
      | return (← introN mvarId 1)
    let domain ← mkAppNS args[2] (args.drop 3)
    let type ← share <| Expr.forallE info domain tp body
    Sym.intros (← mvarId.replaceTargetDefEq type) #[n]
  else
    introN mvarId 1

/--
Post-process a goal produced by `LogicOp.mkBackwardRuleForLogic`.
- `.And`: split `a ∧ b` into two subgoals using `And.intro`.
- `.Imp`: introduce one binder; if its domain is `withName n x`, use name `n`.
-/
def LogicOp.postProcessGoal (lop : LogicOp) (goal : MVarId) : SymM (List MVarId) := do
  match lop with
  | .And => do
    let rule ← mkBackwardRuleFromDecl ``And.intro
    let .goals goals ← rule.apply goal
      | throwError "Failed to apply And.intro to goal {goal.name}"
    return goals
  | .Imp => do
    let IntrosResult.goal _ goal ← intro1WithName goal
      | throwError "Failed to intro implication premise at goal {goal.name}"
    return [goal]

end Loom
