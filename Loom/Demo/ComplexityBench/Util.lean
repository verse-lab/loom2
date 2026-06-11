import Loom.Demo.Complexity

namespace ComplexityBench

/-- Shared worst-case input for all benchmarks: `#[1, 2, ..., n]`, searched for `n`. -/
def mkWorstCaseInput (n : Nat) : Array Nat := Id.run do
  let mut xs := Array.emptyWithCapacity n
  let mut i := 0
  while i < n do
    xs := xs.push (i + 1)
    i := i + 1
  return xs

def parseN (args : List String) : Nat :=
  if h : args.length > 0 then
    (args[0]).toNat?.getD 10000000
  else
    10000000

def linearSearchArrayIdxNoTick? (p : Nat → Bool) (xs : Array Nat) : Option Nat :=
  let rec loop (i : Nat) : Option Nat :=
    if h : i < xs.size then
      if p xs[i] then
        some i
      else
        loop (i + 1)
    else
      none
  loop 0

def runNoTick
    (search : (Nat → Bool) → Array Nat → Option Nat)
    (args : List String) : IO Unit := do
  let n := parseN args
  let xs := mkWorstCaseInput n
  let result := search (fun x => x == n) xs
  IO.println s!"{result}"

def runBasic
    (search : (Nat → Bool) → Array Nat → BasicRepr.CreditT IO (Option Nat))
    (args : List String) : IO Unit := do
  let n := parseN args
  let xs := mkWorstCaseInput n
  let result ← (search (fun x => x == n) xs).run 0
  IO.println s!"{result.fst}"

def runGhostTuple
    (search : (Nat → Bool) → Array Nat → GhostReprTuple.CreditT IO (Option Nat))
    (args : List String) : IO Unit := do
  let n := parseN args
  let xs := mkWorstCaseInput n
  let result ← (search (fun x => x == n) xs).run GhostReprTuple.Credit.default
  IO.println s!"{result.fst}"

def runGhostStructure
    (search : (Nat → Bool) → Array Nat → GhostReprStructure.CreditT IO (Option Nat))
    (args : List String) : IO Unit := do
  let n := parseN args
  let xs := mkWorstCaseInput n
  let result ← (search (fun x => x == n) xs).run GhostReprStructure.Credit.default
  IO.println s!"{result.val}"

def runGhostStateT
    (search : (Nat → Bool) → Array Nat → GhostReprStateT.CreditT IO (Option Nat))
    (args : List String) : IO Unit := do
  let n := parseN args
  let xs := mkWorstCaseInput n
  let result ← (search (fun x => x == n) xs).run GhostReprStateT.Credit.default
  IO.println s!"{result.fst}"

def runGhostStateRefT
    (search : (Nat → Bool) → Array Nat → GhostReprStateRefT.CreditT IO (Option Nat))
    (args : List String) : IO Unit := do
  let n := parseN args
  let xs := mkWorstCaseInput n
  let result ← (search (fun x => x == n) xs).run GhostReprStateRefT.Credit.default
  IO.println s!"{result.fst}"

end ComplexityBench
