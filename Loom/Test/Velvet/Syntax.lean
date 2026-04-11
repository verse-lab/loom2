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
  preNames     : Array Name := #[]   -- names for require clauses
  postNames    : Array Name := #[]   -- names for ensures clauses
  invNames     : Array Name := #[]   -- names for invariant clauses
  isFixpoint   : Bool := false       -- true for method_fix (recursive methods)

/-- Extract invariant names from a doSeq syntax by recursively searching for
    "invariant" atoms in the syntax tree. -/
private partial def extractInvNames (stx : Syntax) : Array Name := Id.run do
  let mut result := #[]
  for node in stx.topDown do
    -- Look for "invariant" atoms — the next sibling(s) determine if named
    if node.isAtom && node.getAtomVal == "invariant" then
      -- We found an "invariant" keyword. The name is tricky to get from just this
      -- atom. Instead, look at the parent structure.
      pure ()
  -- Simpler approach: walk all atoms, collect the ident before ":" that follows "invariant"
  let atoms := collectAtoms stx #[]
  let mut i := 0
  while i < atoms.size do
    if atoms[i]! == "invariant" then
      -- Check if next is an ident followed by ":"
      if i + 2 < atoms.size && atoms[i + 2]! == ":" then
        result := result.push (Name.mkSimple atoms[i + 1]!)
        i := i + 3
      else
        result := result.push (Name.mkSimple s!"invariant{result.size + 1}")
        i := i + 1
    else
      i := i + 1
  return result
where
  collectAtoms (stx : Syntax) (acc : Array String) : Array String :=
    if stx.isAtom then
      acc.push stx.getAtomVal
    else if stx.isIdent then
      acc.push stx.getId.toString
    else
      stx.getArgs.foldl (init := acc) fun acc child => collectAtoms child acc

initialize velvetObligations : EnvExtension (Std.HashMap Name VelvetObligation) ←
  registerEnvExtension (pure {})

private def _root_.Lean.EnvExtension.modify' [Inhabited σ] (ext : EnvExtension σ) [MonadEnv m] (f : σ → σ) : m Unit :=
  Lean.modifyEnv (ext.modifyState · f)

private def _root_.Lean.EnvExtension.get' [Inhabited σ] (ext : EnvExtension σ) [Monad m] [MonadEnv m] : m σ := do
  return ext.getState (← getEnv)

/-! ## While' syntax (partial correctness — no decreasing) -/

/-- Fold invariants into an `InvListWithNames` — a named conjunction list. -/
private def foldInvariants (invs : Array (Lean.TSyntax `term))
    (names : Array (Option Ident) := #[]) : Lean.MacroM (Lean.TSyntax `term) := do
  if invs.isEmpty then `(True)
  else
    let invListOne := mkIdent ``Loom.InvListWithNames.one
    let invListCons := mkIdent ``Loom.InvListWithNames.cons
    -- Build right-nested InvListWithNames: cons h₁ inv₁ (cons h₂ inv₂ (one h₃ inv₃))
    let getName (i : Nat) : Lean.MacroM (Lean.TSyntax `term) := do
      let name := match names[i]? with
        | some (some id) => id.getId.toString
        | _ => s!"invariant{i + 1}"
      let nameStr := Lean.Syntax.mkStrLit name
      `(Lean.Name.mkSimple $nameStr)
    let lastIdx := invs.size - 1
    let mut result ← `($invListOne ($(← getName lastIdx)) $(invs[lastIdx]!))
    for i in List.range lastIdx |>.reverse do
      result ← `($invListCons ($(← getName i)) $(invs[i]!) $result)
    return result

-- While' with optional named invariants: `invariant h : pred` or `invariant pred`
syntax "while' " termBeforeDo
  (" invariant " (atomic(ident " : "))? termBeforeDo)*
  " done_with " termBeforeDo
  " do " doSeq : doElem

syntax "while' " termBeforeDo
  (" invariant " (atomic(ident " : "))? termBeforeDo)*
  " do " doSeq : doElem

-- While' with `decreasing` measure (total correctness): with and without `done_with`
syntax "while' " termBeforeDo
  (" invariant " (atomic(ident " : "))? termBeforeDo)*
  " decreasing " termBeforeDo
  " done_with " termBeforeDo
  " do " doSeq : doElem

syntax "while' " termBeforeDo
  (" invariant " (atomic(ident " : "))? termBeforeDo)*
  " decreasing " termBeforeDo
  " do " doSeq : doElem

macro_rules
  | `(doElem| while' $cond $[ invariant $[$ns : ]? $invs]* decreasing $m done_with $d do $body) => do
    let inv ← foldInvariants invs ns
    `(doElem| repeat do
      invariantGadget $inv
      decreasingGadget $m
      onDoneGadget $d
      if $cond then $body else break)

macro_rules
  | `(doElem| while' $cond $[ invariant $[$ns : ]? $invs]* decreasing $m do $body) => do
    let inv ← foldInvariants invs ns
    `(doElem| repeat do
      invariantGadget $inv
      decreasingGadget $m
      onDoneGadget (¬ $cond)
      if $cond then $body else break)

macro_rules
  | `(doElem| while' $cond $[ invariant $[$ns : ]? $invs]* done_with $d do $body) => do
    let inv ← foldInvariants invs ns
    `(doElem| repeat do
      invariantGadget $inv
      onDoneGadget $d
      if $cond then $body else break)

macro_rules
  | `(doElem| while' $cond $[ invariant $[$ns : ]? $invs]* do $body) => do
    let inv ← foldInvariants invs ns
    `(doElem| repeat do
      invariantGadget $inv
      onDoneGadget (¬ $cond)
      if $cond then $body else break)

/-! ## Array indexing sugar -/

macro_rules
  | `(doElem|$id:ident[$idx:term] := $val:term) =>
    `(doElem| $id:term := Array.set! $id:term $idx $val)

/-! ## Helpers -/

/-- Fold terms into an `InvListWithNames` — a named conjunction list. -/
private def andList (ts : Array (TSyntax `term)) (names : Array Name := #[])
    (pfx : String := "clause") : MacroM (TSyntax `term) := do
  if ts.size = 0 then `(term| True) else
    let invListOne := mkIdent ``Loom.InvListWithNames.one
    let invListCons := mkIdent ``Loom.InvListWithNames.cons
    let getName (i : Nat) : MacroM (TSyntax `term) := do
      let name := if i < names.size then names[i]!.toString else s!"{pfx}{i + 1}"
      let nameStr := Lean.Syntax.mkStrLit name
      `(Lean.Name.mkSimple $nameStr)
    let lastIdx := ts.size - 1
    let mut result ← `($invListOne ($(← getName lastIdx)) $(ts[lastIdx]!))
    for i in List.range lastIdx |>.reverse do
      result ← `($invListCons ($(← getName i)) $(ts[i]!) $result)
    return result

/-! ## `method` command -/

syntax "method " ident bracketedBinder* " return " "(" ident " : " term ")"
  (" require " (atomic(ident " : "))? termBeforeDo)*
  (" ensures " (atomic(ident " : "))? termBeforeDo)* " do " doSeq : command

elab_rules : command
  | `(command|
  method $name:ident $binders:bracketedBinder* return ( $retId:ident : $retType:term )
  $[require $[$reqNs : ]? $req]*
  $[ensures $[$ensNs : ]? $ens]* do $doSeq:doSeq
  ) => do
  let (defCmd, obligation) ← Command.runTermElabM fun _vs => do
    -- Collect parameter identifiers
    let mut ids : Array Ident := #[]
    for b in binders do
      match b with
      | `(bracketedBinder| ($id:ident : $_:term)) => ids := ids.push id
      | `(bracketedBinder| {$id:ident : $_:term}) => ids := ids.push id
      | _ => throwError "unexpected binder syntax: {b}"
    -- Extract names
    let mut reqNames : Array Name := #[]
    for idx in [:reqNs.size] do
      reqNames := reqNames.push <| match reqNs[idx]! with
        | some id => id.getId
        | none => Name.mkSimple s!"require{idx + 1}"
    let mut ensNames : Array Name := #[]
    for idx in [:ensNs.size] do
      ensNames := ensNames.push <| match ensNs[idx]! with
        | some id => id.getId
        | none => Name.mkSimple s!"ensures{idx + 1}"
    -- Build pre/post with WithHypName annotations
    let pre ← liftMacroM <| andList req reqNames "require"
    let post ← liftMacroM <| andList ens ensNames "ensures"
    -- Build definition
    let defCmd ← `(command|
      set_option linter.unusedVariables false in
      def $name $binders* : Option $retType:term := do $doSeq)
    -- Extract invariant names from the do-block syntax
    let invNames := extractInvNames doSeq.raw
    let obligation : VelvetObligation := {
      binderIdents := binders
      ids := ids
      retId := retId
      pre := pre
      post := post
      preNames := reqNames
      postNames := ensNames
      invNames := invNames
    }
    return (defCmd, obligation)
  elabCommand defCmd
  velvetObligations.modify' (·.insert name.getId obligation)

/-! ## `method_fix` command (recursive methods) -/

syntax "method_fix " ident bracketedBinder* " return " "(" ident " : " term ")"
  (" require " (atomic(ident " : "))? termBeforeDo)*
  (" ensures " (atomic(ident " : "))? termBeforeDo)* " do " doSeq : command

elab_rules : command
  | `(command|
  method_fix $name:ident $binders:bracketedBinder* return ( $retId:ident : $retType:term )
  $[require $[$reqNs : ]? $req]*
  $[ensures $[$ensNs : ]? $ens]* do $doSeq:doSeq
  ) => do
  let (defCmd, obligation) ← Command.runTermElabM fun _vs => do
    let mut ids : Array Ident := #[]
    for b in binders do
      match b with
      | `(bracketedBinder| ($id:ident : $_:term)) => ids := ids.push id
      | `(bracketedBinder| {$id:ident : $_:term}) => ids := ids.push id
      | _ => throwError "unexpected binder syntax: {b}"
    let mut reqNames : Array Name := #[]
    for idx in [:reqNs.size] do
      reqNames := reqNames.push <| match reqNs[idx]! with
        | some id => id.getId
        | none => Name.mkSimple s!"require{idx + 1}"
    let mut ensNames : Array Name := #[]
    for idx in [:ensNs.size] do
      ensNames := ensNames.push <| match ensNs[idx]! with
        | some id => id.getId
        | none => Name.mkSimple s!"ensures{idx + 1}"
    let pre ← liftMacroM <| andList req reqNames "require"
    let post ← liftMacroM <| andList ens ensNames "ensures"
    -- Build recursive definition with partial_fixpoint
    let defCmd ← `(command|
      set_option linter.unusedVariables false in
      def $name $binders* : Option $retType:term := do $doSeq
        partial_fixpoint)
    let invNames := extractInvNames doSeq.raw
    let obligation : VelvetObligation := {
      binderIdents := binders
      ids := ids
      retId := retId
      pre := pre
      post := post
      preNames := reqNames
      postNames := ensNames
      invNames := invNames
      isFixpoint := true
    }
    return (defCmd, obligation)
  elabCommand defCmd
  velvetObligations.modify' (·.insert name.getId obligation)

/-! ## `prove_correct` / `prove_correct?` / `prove_correct_total` commands -/

syntax "prove_correct " ident " by " tacticSeq : command
syntax "prove_correct? " ident : command
syntax "prove_correct_total " ident " by " tacticSeq : command

private def mkProveCorrectThm (name : Ident) (obligation : VelvetObligation)
    (proof? : Option (TSyntax ``Lean.Parser.Tactic.tacticSeq))
    (total : Bool := false) : CommandElabM (TSyntax `command) := do
  let bindersIdents := obligation.binderIdents
  let ids := obligation.ids
  let retId := obligation.retId
  let pre := obligation.pre
  let post := obligation.post
  let lemmaName := mkIdent <| name.getId.appendAfter "_correct"
  let tripleId := mkIdent ``Triple
  let tripleFromPC := mkIdent ``triple_from_option_spec
  let pcName := mkIdent <| name.getId ++ `partial_correctness
  let ihName := mkIdent <| name.getId.appendAfter "_ih"
  let ihRawName := mkIdent (Name.mkSimple s!"ih_{name.getId}_raw")
  let ihTripleName := mkIdent (Name.mkSimple s!"ih_{name.getId}")
  let tripleFromPC' := mkIdent ``triple_from_option_spec
  -- Epost expression: True for partial, False for total.
  let epostStx ← if total then `((False : Prop)) else `((True : Prop))
  if obligation.isFixpoint then
    if total then
      throwError "prove_correct_total not yet supported for recursive (method_fix) methods"
    -- For fixpoint methods:
    -- 1. Apply triple_from_option_spec outside GrindM to convert Triple → equation
    -- 2. Apply partial_correctness outside GrindM for induction
    -- 3. Intro f_ih + raw IH outside GrindM
    -- 4. Convert IH to Triple form (have ih_triple)
    -- 5. Convert goal back to Triple via triple_to_option_spec
    -- 6. simp only [name] to unfold the fixpoint body
    -- 7. User's mvcgen' runs INSIDE GrindM with ih_triple as a local spec
    --
    -- Steps 1-5 run OUTSIDE GrindM (at the MetaM/tactic level).
    -- Step 7 runs INSIDE GrindM where ih_triple is a local fvar visible to the kernel.
    let ihConversion ← `(fun $ids* => $tripleFromPC' ($ihRawName $ids*))
    let tripleToPC := mkIdent ``triple_to_option_spec
    match proof? with
    | some proof =>
      `(command|
        set_option linter.unusedVariables false in
        theorem $lemmaName $bindersIdents* :
          $tripleId
            $pre
            ($name $ids*)
            (fun $retId => $post) $epostStx := by
          apply $tripleFromPC
          apply $pcName
          intro $ihName $ihRawName
          have $ihTripleName := $ihConversion
          intro $ids*
          exact $tripleToPC (by ($proof)))
    | none =>
      `(command|
        set_option linter.unusedVariables false in
        theorem $lemmaName $bindersIdents* :
          $tripleId
            $pre
            ($name $ids*)
            (fun $retId => $post) $epostStx := by
          apply $tripleFromPC
          apply $pcName
          intro $ihName $ihRawName
          have $ihTripleName := $ihConversion
          intro $ids*
          exact $tripleToPC (by sorry))
  else
    -- For non-recursive methods: unfold with simp, then user's proof
    match proof? with
    | some proof =>
      `(command|
        set_option linter.unusedVariables false in
        theorem $lemmaName $bindersIdents* :
          $tripleId
            $pre
            ($name $ids*)
            (fun $retId => $post) $epostStx := by
          simp only [$name:ident]
          ($proof))
    | none =>
      `(command|
        set_option linter.unusedVariables false in
        theorem $lemmaName $bindersIdents* :
          $tripleId
            $pre
            ($name $ids*)
            (fun $retId => $post) $epostStx := by
          simp only [$name:ident]
          sorry)

@[incremental]
elab_rules : command
  | `(command| prove_correct $name:ident by $proof:tacticSeq) => do
    let ctx ← velvetObligations.get'
    let .some obligation := ctx[name.getId]?
      | throwError "no obligation found for `{name.getId}`. Did you define it with `method`?"
    -- Extract MProd component names from the method definition for variable naming
    let mprodNames ← Command.runTermElabM fun _ => do
      Loom.extractMProdNamesFromDef name.getId
    Loom.mProdNameHintsRef.set mprodNames
    -- Store clause names for hypothesis naming
    Loom.clauseNameHintsRef.set {
      preNames := obligation.preNames
      postNames := obligation.postNames
      invNames := obligation.invNames
    }
    let thmCmd ← mkProveCorrectThm name obligation (some proof)
    elabCommand thmCmd
    velvetObligations.modify' (·.erase name.getId)

@[incremental]
elab_rules : command
  | `(command| prove_correct? $name:ident) => do
    let ctx ← velvetObligations.get'
    let .some obligation := ctx[name.getId]?
      | throwError "no obligation found for `{name.getId}`. Did you define it with `method`?"
    let thmCmd ← mkProveCorrectThm name obligation none
    Command.liftTermElabM do
      Lean.Meta.Tactic.TryThis.addSuggestion (← getRef) thmCmd

@[incremental]
elab_rules : command
  | `(command| prove_correct_total $name:ident by $proof:tacticSeq) => do
    let ctx ← velvetObligations.get'
    let .some obligation := ctx[name.getId]?
      | throwError "no obligation found for `{name.getId}`. Did you define it with `method`?"
    -- Extract MProd component names from the method definition for variable naming
    let mprodNames ← Command.runTermElabM fun _ => do
      Loom.extractMProdNamesFromDef name.getId
    Loom.mProdNameHintsRef.set mprodNames
    -- Store clause names for hypothesis naming
    Loom.clauseNameHintsRef.set {
      preNames := obligation.preNames
      postNames := obligation.postNames
      invNames := obligation.invNames
    }
    let thmCmd ← mkProveCorrectThm name obligation (some proof) (total := true)
    elabCommand thmCmd
    velvetObligations.modify' (·.erase name.getId)
