import Lean
import Lean.Parser
import Loom.Test.Velvet.Theory
import Loom.Test.Velvet.Utils

open Lean Elab Command Term Meta Lean.Parser Lean.Macro Std.Do'

/-! ## Environment extension for method obligations -/

structure Obligations where
  binderIdents : Array (TSyntax `Lean.Parser.Term.bracketedBinder)
  ids          : Array Ident
  retId        : Ident
  pre          : TSyntax `term
  post         : TSyntax `term
  isFixpoint   : Bool := false

initialize obligations : EnvExtension (Std.HashMap Name Obligations) ←
  registerEnvExtension (pure {})

private def _root_.Lean.EnvExtension.modify' [Inhabited σ] (ext : EnvExtension σ)
    [MonadEnv m] (f : σ → σ) : m Unit :=
  Lean.modifyEnv (ext.modifyState · f)

private def _root_.Lean.EnvExtension.get' [Inhabited σ] (ext : EnvExtension σ)
    [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (← getEnv)


syntax "while " (atomic(ident " : "))? termBeforeDo
  (" invariant " (atomic(ident " : "))? termBeforeDo)*
  " decreasing " (atomic(ident " : ")? termBeforeDo )
  (" done_with " (atomic(ident " : ")? termBeforeDo  ("by " tacticSeq)?))?
  " do " doSeq : doElem

syntax "method " ("rec ")? ident bracketedBinder* " returns " "(" ident " : " term ")"
  (" requires " (atomic(ident " : "))? termBeforeDo)*
  (" ensures " (atomic(ident " : "))? termBeforeDo)* " do " doSeq : command

set_option linter.unusedVariables false in
elab_rules : command
  | `(command|
      method $[rec%$recTk]? $name:ident $binders:bracketedBinder* returns ($retId:ident : $retType:term)
        $[requires $[$reqNs : ]? $req]*
        $[ensures $[$ensNs : ]? $ens]* do $body:doSeq) => do
    let (defCmd, obligation) ← Command.runTermElabM fun _vs => do
      let mut ids : Array Ident := #[]
      for b in binders do
        match b with
        | `(bracketedBinder| ($id:ident : $_:term)) => ids := ids.push id
        | `(bracketedBinder| {$id:ident : $_:term}) => ids := ids.push id
        | _ => throwErrorAt b "unexpected binder syntax"

      let mut reqNames : Array Name := #[]
      for idx in [:reqNs.size] do
        reqNames := reqNames.push <| match reqNs[idx]! with
          | some id => id.getId
          | none => Name.mkSimple s!"requires{idx + 1}"

      let mut ensNames : Array Name := #[]
      for idx in [:ensNs.size] do
        ensNames := ensNames.push <| match ensNs[idx]! with
          | some id => id.getId
          | none => Name.mkSimple s!"ensures{idx + 1}"

      let pre ← liftMacroM <| andList req reqNames "requires"
      let post ← liftMacroM <| andList ens ensNames "ensures"
      let defCmd ←
        if recTk.isSome then
          `(command|
            set_option linter.unusedVariables false in
            def $name $binders* : Option $retType:term := do $body
              partial_fixpoint)
        else
          `(command|
            set_option linter.unusedVariables false in
            def $name $binders* : Option $retType:term := do $body)
      let obligation : Obligations := {
        binderIdents := binders
        ids := ids
        retId := retId
        pre := pre
        post := post
      }
      return (defCmd, obligation)
    elabCommand defCmd
    let declName ← liftCoreM <| realizeGlobalConstNoOverload name
    let isRec ← liftCoreM <| isRecursiveDefinition declName
    match recTk, isRec with
    | some recStx, false =>
        logWarningAt recStx "unneeded `rec`; this method is not recursive, please remove it"
    | none, true =>
        throwErrorAt name "recursive method `{declName}` requires `rec`; write `method rec {name.getId} ...`"
    | _, _ => pure ()
    obligations.modify' (·.insert declName { obligation with isFixpoint := isRec })


syntax "prove_correct " ident " by " tacticSeq : command

private def mkProveCorrectThm (name : Ident) (obligation : Obligations)
    (proof : TSyntax ``Lean.Parser.Tactic.tacticSeq) : CommandElabM (TSyntax `command) := do
  let binders := obligation.binderIdents
  let ids := obligation.ids
  let retId := obligation.retId
  let pre := obligation.pre
  let post := obligation.post
  let lemmaName := mkIdent <| name.getId.appendAfter "_correct"
  let tripleId := mkIdent ``Triple
  if obligation.isFixpoint then
    let tripleFromPC := mkIdent ``triple_from_option_spec
    let tripleToPC := mkIdent ``triple_to_option_spec
    let pcName := mkIdent <| name.getId ++ `partial_correctness
    let ihName := mkIdent <| name.getId.appendAfter "_ih"
    let ihRawName := mkIdent <| Name.mkSimple s!"ih_{name.getId}_raw"
    let ihTripleName := mkIdent <| Name.mkSimple s!"ih_{name.getId}"
    let ihConversion ← `(fun $ids* => $tripleFromPC ($ihRawName $ids*))
    `(
      command|
      set_option linter.unusedVariables false in
      @[lspec]
      theorem $lemmaName $binders* :
        $tripleId
          $pre
          ($name $ids*)
          (fun $retId => $post)
          (True : Prop) := by
        apply $tripleFromPC
        apply $pcName
        intro $ihName $ihRawName
        have $ihTripleName := $ihConversion
        intro $ids*
        exact $tripleToPC (by
          ($proof)))
  else
    `(
      command|
      set_option linter.unusedVariables false in
      @[lspec]
      theorem $lemmaName $binders* :
        $tripleId
          $pre
          ($name $ids*)
          (fun $retId => $post)
          (True : Prop) := by
        simp only [$name:ident]
        ($proof))

@[incremental]
elab_rules : command
  | `(command| prove_correct $name:ident by $proof:tacticSeq) => do
    let ctx ← obligations.get'
    let declName ← liftCoreM <| realizeGlobalConstNoOverload name
    let .some obligation := ctx[declName]?
      | throwError "no obligation found for `{name.getId}`. Did you define it with `method`?"
    let mprodNames ← Command.runTermElabM fun _ => do
      Loom.extractMProdNamesFromDef declName
    Loom.mProdNameHintsRef.set mprodNames
    let thmCmd ← mkProveCorrectThm name obligation proof
    elabCommand thmCmd
    obligations.modify' (·.erase declName)


macro_rules
  | `(doElem| while $[$hcond : ]? $cond $[ invariant $[$ns : ]? $invs]* decreasing $[$hm : ]? $m $[done_with $[$h_done : ]? $d]? do $body) => do
  let defaultLoopIdent := mkIdent `h_loop
  let loopIdent := hcond.getD defaultLoopIdent


  let invs' <- foldInvariants invs ns

  let default_done_with: TSyntax `term ← withRef cond do `(¬ $cond)
  let doneWith := d.getD default_done_with

  -- TODO: Re-enable this once `done_with` names are introduced properly by vcgen.
  -- let defaultDoneWithIdent := mkIdent `h_done_with
  -- let doneWithIdent := (h_done.join.getD defaultDoneWithIdent)
  -- let doneWithNameStr := Lean.Syntax.mkStrLit doneWithIdent.getId.toString
  -- let doneWithNameTerm : TSyntax `term ← `(Lean.Name.mkSimple $doneWithNameStr)
  -- let invListOne := mkIdent ``Loom.InvListWithNames.one
  -- let doneWithNamed : TSyntax `term ← `($invListOne $doneWithNameTerm $doneWith)

  -- TODO: Think about this
  -- Ideally, when the loop finishes, we want it to return the done_with condition.
  -- That way it's available in the program to the next construct.
  -- However, it's quite easy for the end user to assert the done_with condition themselves
  -- if they want it in the Lean program context..
  -- They can easily also write an `if h: <done_with>` and proceed, since termination
  -- of the loop guarantees the done_with condition, we always show that in the proof..
  `(doElem| repeat do
    invariantGadget $invs'
    decreasingGadget $m
    -- Use `$doneWithNamed` here once named `done_with` hypotheses are supported.
    onDoneGadget $doneWith
        if $loopIdent : $cond then $body else break
    )

  /- Lean.Macro.throwErrorAt doneWith s!"Testing: {doneWith}" -/

#check Loop.mk

def foo : Id Nat := do
    let mut i := 0
    for _ in  Loop.mk do
        if i < 1 then
           i := i + 1
        else
            break
    /- repeat do
     -     pure ()
     -     -- Use `$doneWithNamed` here once named `done_with` hypotheses are supported.
     -     pure ()
     -     if h : i < 1 then
     -        i := i + 1
     -     else break -/


    return 10

#eval foo.run
