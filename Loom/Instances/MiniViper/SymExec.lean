import Loom.Instances.MiniViper.Syntax
import Loom.Instances.MiniViper.SymState

open SExp


def shiftAndAdd (store : List (Option α)) (v : α) : List (Option α) :=
  some v :: store


partial def sexecExp (σ : SymState) (e : PureExp) (K : SymState → SExp → Bool) : Bool :=
  match e with
  | .eLit l =>
    K σ (sLit (valOfLit l))

  | .var x =>
    match σ.storeLookup x with
    | some t => K σ t
    | none => false

  | .unop op e =>
    sexecExp σ e fun σ t => K σ (.sUnop op t)

  | .binop e1 op e2 =>
    sexecExp σ e1 fun σ t1 =>
      match binopLazyBool op with
      | some bres =>

        K (σ.condAdd (sEq t1 (sBool bres.1))) (sBool bres.2) &&
        sexecExp (σ.condAdd (sEq t1 (sNot (sBool bres.1)))) e2 K
      | none =>

        sexecExp σ e2 fun σ t2 =>
          symImplies σ.cond (.sBinopSafe t1 op t2) &&
          K σ (.sBinop t1 op t2)

  | .condExp e1 e2 e3 =>
    sexecExp σ e1 fun σ t1 =>
      sexecExp (σ.condAdd t1) e2 K &&
      sexecExp (σ.condAdd (sNot t1)) e3 K

  | .fieldAcc e f =>
    sexecExp σ e fun σ te =>
      match symHeapExtract σ te f (some (sPerm 0)) with
      | some (σ', c) =>
        let σ'' := symHeapDoAdd σ' c
        K σ'' c.val
      | none => false


partial def sproduce (σ : SymState) (A : Assert) (K : SymState → Bool) : Bool :=
  match A with
  | .atomic (.pure e) =>
    sexecExp σ e fun σ t => K (σ.condAdd t)

  | .atomic (.acc e f (.pureExp ep)) =>
    sexecExp σ e fun σ te =>
    sexecExp σ ep fun σ tep =>

      symImplies σ.cond (sNot (sEq tep (sPerm 0))) &&
      match σ.fieldLookup f with
      | some ty =>
        let (σ', tv) := σ.genFresh ty
        let σ'' := symHeapDoAdd σ' ⟨f, te, tep, .sVar tv⟩
        K σ''
      | none => false

  | .atomic (.acc e f .wildcard) =>
    sexecExp σ e fun σ te =>
      let (σ', tp) := σ.genFresh .tPerm
      match σ'.fieldLookup f with
      | some ty =>
        let (σ'', tv) := σ'.genFresh ty
        let σ''' := σ''.condAdd (sLt (sPerm 0) (.sVar tp))
        let σ'''' := symHeapDoAdd σ''' ⟨f, te, .sVar tp, .sVar tv⟩
        K σ''''
      | none => false

  | .star a1 a2 =>
    sproduce σ a1 fun σ => sproduce σ a2 K

  | .imp e a =>
    sexecExp σ e fun σ t =>
      K (σ.condAdd (sNot t)) &&
      sproduce (σ.condAdd t) a K

  | .condAssert e a1 a2 =>
    sexecExp σ e fun σ t =>
      sproduce (σ.condAdd t) a1 K &&
      sproduce (σ.condAdd (sNot t)) a2 K


partial def sconsume (σ : SymState) (A : Assert) (K : SymState → Bool) : Bool :=
  match A with
  | .atomic (.pure e) =>
    sexecExp σ e fun σ t =>
      symImplies σ.cond t && K σ

  | .atomic (.acc e f (.pureExp ep)) =>
    sexecExp σ e fun σ te =>
    sexecExp σ ep fun σ tep =>
      match symHeapExtract σ te f (some tep) with
      | some (σ', c) =>
        let σ'' := symHeapDoAdd σ' { c with perm := sSub c.perm tep }
        K σ''
      | none => false

  | .atomic (.acc e f .wildcard) =>
    sexecExp σ e fun σ te =>
      match symHeapExtract σ te f none with
      | some (σ', c) =>
        let σ'' := symHeapDoAdd σ' { c with perm := sPermDiv c.perm (sPerm 2) }
        K σ''
      | none => false

  | .star a1 a2 =>
    sconsume σ a1 fun σ => sconsume σ a2 K

  | .imp e a =>
    sexecExp σ e fun σ t =>
      K (σ.condAdd (sNot t)) &&
      sconsume (σ.condAdd t) a K

  | .condAssert e a1 a2 =>
    sexecExp σ e fun σ t =>
      sconsume (σ.condAdd t) a1 K &&
      sconsume (σ.condAdd (sNot t)) a2 K


partial def sexec (σ : SymState) (s : Stmt) (K : SymState → Bool) : Bool :=
  match s with
  | .skip => K σ

  | .inhale a => sproduce σ a K

  | .exhale a =>
    sconsume σ a fun σ =>
      match symStabilize σ with
      | some σ' => K σ'
      | none => false

  | .seq s1 s2 =>
    sexec σ s1 fun σ => sexec σ s2 K

  | .ite e s1 s2 =>
    sexecExp σ e fun σ t =>
      sexec (σ.condAdd t) s1 K &&
      sexec (σ.condAdd (sNot t)) s2 K

  | .localAssign v e =>
    match σ.storeLookup v with
    | some _ =>
      sexecExp σ e fun σ t =>
        K (σ.storeUpdate v t)
    | none => false

  | .havoc v =>
    if h : v < σ.storeType.length then
      match σ.storeType[v] with
      | some ty =>
        let (σ', t) := σ.genFresh ty
        K (σ'.storeUpdate v (.sVar t))
      | none => false
    else false

  | .fieldAssign e f e2 =>
    sexecExp σ e fun σ t =>
    sexecExp σ e2 fun σ t2 =>
      match symHeapExtract σ t f (some (sPerm 1)) with
      | some (σ', c) =>
        match symStabilize σ' with
        | some σ'' =>
          let σ''' := symHeapDoAdd σ'' { c with val := t2 }
          K σ'''
        | none => false
      | none => false


partial def sinit (params : List VTyp) (fields : List (FieldName × VTyp))
    (K : SymState → Bool) : Bool :=
  let emptyState : SymState := {
    store := []
    cond := sBool true
    heap := []
    used := 0
    storeType := []
    fields := fields
  }
  go params emptyState K
where
  go : List VTyp → SymState → (SymState → Bool) → Bool
  | [], σ, K => K σ
  | ty :: rest, σ, K =>
    go rest σ fun σ =>
      let (σ', v) := σ.genFresh ty
      K { σ' with
        store := shiftAndAdd σ'.store (.sVar v)
        storeType := shiftAndAdd σ'.storeType ty
      }
