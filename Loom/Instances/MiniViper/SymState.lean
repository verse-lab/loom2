import Loom.Instances.MiniViper.SExp

open SExp


structure Chunk where
  field : FieldName
  recv  : SExp
  perm  : SExp
  val   : SExp
  deriving Repr, BEq


structure SymState where
  store     : List (Option SExp)
  cond      : SExp
  heap      : List Chunk
  used      : Nat
  storeType : List (Option VTyp)
  fields    : List (FieldName × VTyp)
  deriving BEq

instance : Repr SymState where
  reprPrec s _ :=
    f!"⟨store={repr s.store}, cond={repr s.cond}, heap={repr s.heap}, used={s.used}, fields={repr s.fields}⟩"

namespace SymState


def fieldLookup (σ : SymState) (f : FieldName) : Option VTyp :=
  (σ.fields.find? (·.1 == f)).map (·.2)


def condAdd (σ : SymState) (t : SExp) : SymState :=
  { σ with cond := sAnd t σ.cond }


def condAddMany (σ : SymState) (ts : List SExp) : SymState :=
  ts.foldl (fun acc t => acc.condAdd t) σ


def fresh (σ : SymState) : Nat := σ.used


def genFresh (σ : SymState) (ty : VTyp) : SymState × Nat :=
  let v := σ.fresh
  let σ' := { σ with used := σ.used + 1 }
  let σ'' := σ'.condAdd (.sHasType ty v)
  (σ'', v)


def storeLookup (σ : SymState) (n : Nat) : Option SExp :=
  match σ.store[n]? with
  | some (some t) => some t
  | _ => none


def storeUpdate (σ : SymState) (n : Nat) (v : SExp) : SymState :=
  { σ with store := σ.store.set n (some v) }

end SymState


def permExceeds1 (p1 p2 : SExp) : Bool :=
  match p1, p2 with
  | .sLit (.vPerm r1), .sLit (.vPerm r2) => decide (r1 + r2 > 1)
  | _, _ => false


def permIsZero (pc : SExp) (p : SExp) : Bool :=
  match p with
  | .sLit (.vPerm r) => decide (r ≤ 0)
  | _ => symImplies pc (sLte p (sPerm 0))


def canMerge (pc : SExp) (c d : Chunk) : Bool :=
  c.field == d.field &&
  symImplies pc (sEq c.recv d.recv) /-&&
  c.val == d.val-/


def mergeChunks (c d : Chunk) : Chunk :=
  { field := c.field
  , recv  := c.recv
  , perm  := sAdd c.perm d.perm
  , val   := c.val
  }


def mergePass (pc : SExp) (heap : List Chunk) : List Chunk :=
  let rec insertChunk (acc : List Chunk) (c : Chunk) : List Chunk :=
    match acc with
    | [] => [c]
    | d :: ds =>
      if canMerge pc c d then
        mergeChunks c d :: ds
      else
        d :: insertChunk ds c
  heap.foldl insertChunk []

def inferDisequalities (pc : SExp) (heap : List Chunk) : List SExp :=
  let rec go : List Chunk → List SExp
    | [] => []
    | c :: rest =>
      let here :=
        rest.filterMap fun d =>
          if c.field == d.field && permExceeds1 c.perm d.perm then
            let diseq := sNot (sEq c.recv d.recv)
            if symImplies pc diseq then none else some diseq
          else
            none
      here ++ go rest
  go heap

def assumeValidPermissions (pc : SExp) (heap : List Chunk) : List SExp :=
  heap.filterMap fun c =>
    let fact := sLte c.perm (sPerm 1)
    if symImplies pc fact then none else some fact


def cleanupHeap (pc : SExp) (heap : List Chunk) : List Chunk :=
  heap.filter (fun c => !permIsZero pc c.perm)


def consolidateStep (σ : SymState) : SymState :=
  let heap₁ := mergePass σ.cond σ.heap
  let facts₂ := inferDisequalities σ.cond heap₁
  let σ₂ := σ.condAddMany facts₂
  let facts₃ := assumeValidPermissions σ₂.cond heap₁
  let σ₃ := σ₂.condAddMany facts₃
  let heap₄ := cleanupHeap σ₃.cond heap₁
  { σ₃ with heap := heap₄ }


def consolidate (σ : SymState) : SymState :=
  let fuel := σ.heap.length * 2 + 8
  let rec loop (n : Nat) (cur : SymState) : SymState :=
    match n with
    | 0 => cur
    | n + 1 =>
      let nxt := consolidateStep cur
      if nxt == cur then cur else loop n nxt
  loop fuel σ


def symHeapDoAdd (σ : SymState) (c : Chunk) : SymState :=
  consolidate { σ with heap := c :: σ.heap }


def symStabilize (σ : SymState) : Option SymState :=
  let σ' := consolidate σ
  if σ'.heap.all (fun c => symImplies σ'.cond (sLt (sPerm 0) c.perm)) then
    some σ'
  else
    none


def checkPermission (pc : SExp) (chunkPerm : SExp) (requested : Option SExp) : Bool :=
  match requested with
  | some tp =>
    symImplies pc (sAnd (sLte (sPerm 0) tp) (sLte tp chunkPerm))
  | none =>
    symImplies pc (sLt (sPerm 0) chunkPerm)


def symHeapExtract (σ : SymState) (recv : SExp) (f : FieldName)
    (minPerm : Option SExp) : Option (SymState × Chunk) :=
  let σ' := consolidate σ
  go σ' σ'.heap [] recv f minPerm
where
  go (σ : SymState) :
      List Chunk → List Chunk → SExp → FieldName → Option SExp →
      Option (SymState × Chunk)
    | [], _, _, _, _ => none
    | c :: rest, before, recv, f, minPerm =>
      if c.field == f &&
         symImplies σ.cond (sEq recv c.recv) &&
         checkPermission σ.cond c.perm minPerm then
        let newHeap := before.reverse ++ rest
        some ({ σ with heap := newHeap }, c)
      else
        go σ rest (c :: before) recv f minPerm
