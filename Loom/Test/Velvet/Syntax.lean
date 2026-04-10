/-
Velvet Syntax: method/prove_correct commands and while' loop macro.
-/
import Lean
import Loom.Test.Velvet.Theory
import Loom.LatticeExt

open Lean Elab Command Term Meta Std.Do' Order Loom Lean.Order

/-! ## Environment extension for method obligations -/

def meetConst : Ident := mkIdent ``meet

structure VelvetObligation where
  binderIdents : Array (TSyntax `Lean.Parser.Term.bracketedBinder)
  ids          : Array Ident
  retId        : Ident
  pre          : TSyntax `term
  post         : TSyntax `term

initialize velvetObligations : EnvExtension (Std.HashMap Name VelvetObligation) ←
  registerEnvExtension (pure {})

private def _root_.Lean.EnvExtension.modify' [Inhabited σ] (ext : EnvExtension σ) [MonadEnv m] (f : σ → σ) : m Unit :=
  Lean.modifyEnv (ext.modifyState · f)

private def _root_.Lean.EnvExtension.get' [Inhabited σ] (ext : EnvExtension σ) [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (← getEnv)

/-! ## While' syntax (partial correctness — no decreasing) -/

private def foldInvariants (invs : Array (Lean.TSyntax `term)) : Lean.MacroM (Lean.TSyntax `term) := do
  if invs.isEmpty then `(True)
  else
    let mut result := invs[0]!
    for i in [1:invs.size] do
      result ← `($meetConst $result $(invs[i]!))
    return result

syntax "while' " termBeforeDo
  (" invariant " termBeforeDo)*
  " done_with " termBeforeDo
  " do " doSeq : doElem

syntax "while' " termBeforeDo
  (" invariant " termBeforeDo)*
  " do " doSeq : doElem

macro_rules
  | `(doElem| while' $cond $[ invariant $invs]* done_with $d do $body) => do
    let inv ← foldInvariants invs
    `(doElem| repeat do
      invariantGadget $inv
      onDoneGadget $d
      if $cond then $body else break)

macro_rules
  | `(doElem| while' $cond $[ invariant $invs]* do $body) => do
    let inv ← foldInvariants invs
    `(doElem| repeat do
      invariantGadget $inv
      onDoneGadget (¬ $cond)
      if $cond then $body else break)

/-! ## Array indexing sugar -/

macro_rules
  | `(doElem|$id:ident[$idx:term] := $val:term) =>
    `(doElem| $id:term := Array.set! $id:term $idx $val)

/-! ## Helpers -/

private def andList (ts : Array (TSyntax `term)) : MacroM (TSyntax `term) := do
  if ts.size = 0 then `(term| True) else
    let mut t := ts[0]!
    for t' in ts[1:] do
      t ← `(term|$meetConst $t' $t)
    return t

/-! ## `method` command -/

syntax "method " ident bracketedBinder* " return " "(" ident " : " term ")"
  (" require " termBeforeDo)*
  (" ensures " termBeforeDo)* " do " doSeq : command

elab_rules : command
  | `(command|
  method $name:ident $binders:bracketedBinder* return ( $retId:ident : $retType:term )
  $[require $req:term]*
  $[ensures $ens:term]* do $doSeq:doSeq
  ) => do
  let (defCmd, obligation) ← Command.runTermElabM fun _vs => do
    -- Collect parameter identifiers
    let mut ids : Array Ident := #[]
    for b in binders do
      match b with
      | `(bracketedBinder| ($id:ident : $_:term)) => ids := ids.push id
      | `(bracketedBinder| {$id:ident : $_:term}) => ids := ids.push id
      | _ => throwError "unexpected binder syntax: {b}"
    -- Build pre/post
    let pre ← liftMacroM <| andList req
    let post ← liftMacroM <| andList ens
    -- Build definition
    let defCmd ← `(command|
      set_option linter.unusedVariables false in
      def $name $binders* : Option $retType:term := do $doSeq)
    let obligation : VelvetObligation := {
      binderIdents := binders
      ids := ids
      retId := retId
      pre := pre
      post := post
    }
    return (defCmd, obligation)
  elabCommand defCmd
  velvetObligations.modify' (·.insert name.getId obligation)

/-! ## `prove_correct` command -/

syntax "prove_correct " ident " by " tacticSeq : command

@[incremental]
elab_rules : command
  | `(command| prove_correct $name:ident by $proof:tacticSeq) => do
    let ctx ← velvetObligations.get'
    let .some obligation := ctx[name.getId]?
      | throwError "no obligation found for `{name.getId}`. Did you define it with `method`?"
    let bindersIdents := obligation.binderIdents
    let ids := obligation.ids
    let retId := obligation.retId
    let pre := obligation.pre
    let post := obligation.post
    let lemmaName := mkIdent <| name.getId.appendAfter "_correct"
    let tripleId := mkIdent ``Triple
    let thmCmd ← `(command|
      set_option linter.unusedVariables false in
      theorem $lemmaName $bindersIdents* :
        $tripleId
          $pre
          ($name $ids*)
          (fun $retId => $post) (True : Prop) := by
        simp only [$name:ident]
        ($proof))
    elabCommand thmCmd
    velvetObligations.modify' (·.erase name.getId)
