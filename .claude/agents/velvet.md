# Velvet — Program Verification DSL for Lean 4

Velvet is a shallow-embedded DSL for verifying imperative programs in Lean 4, built on top of the Loom2 weakest-precondition framework.

## Quick Start

```lean
import Loom.Test.Velvet.Syntax

method isEven (n : Nat) return (result : Bool)
  ensures h : result = (n % 2 == 0)
  do
  return n % 2 == 0

prove_correct isEven by
  mvcgen' simplifying_assumptions with grind
```

## Core Concepts

### Methods

Define imperative programs with `method`:

```lean
method name (params) return (retId : RetType)
  require h_pre : precondition    -- optional, named preconditions
  ensures h_post : postcondition  -- named postconditions
  do
    body
```

- The method elaborates to `def name params : Option RetType := do body`
- `require` clauses become preconditions (conjunction)
- `ensures` clauses become postconditions (conjunction)
- Names (`h_pre :`, `h_post :`) are optional — if omitted, auto-generated as `require1`, `ensures1`, etc.
- Names appear as hypothesis names in proof goals

### Recursive Methods

Use `method_fix` for recursive functions:

```lean
method_fix gcd (a : Nat) (b : Nat) return (res : Nat)
  ensures h : res = Nat.gcd a b
  do
    if b = 0 then return a
    else
      let r ← gcd b (a % b)
      return r
```

- Elaborates with `partial_fixpoint` (partial correctness semantics)
- Lean auto-generates `gcd.partial_correctness` induction principle
- `prove_correct` auto-applies the induction and provides the IH to `mvcgen'`

### Loops

Use `while'` for loops with named invariants:

```lean
while' i < n
  invariant h_bound : i ≤ n
  invariant h_sum : s = (List.range i).sum
  done_with i = n
do
  s := s + i
  i := i + 1
```

- `invariant h : pred` — named loop invariant (name appears in proof goals)
- `done_with expr` — condition that holds when loop exits (optional; defaults to `¬ cond`)
- Multiple mutable variables are supported (packed into `MProd` internally, split automatically by VCGen)

### Proving Correctness

```lean
prove_correct methodName by
  mvcgen' simplifying_assumptions with grind
```

- `mvcgen'` — the main VCGen tactic that decomposes the Triple into verification conditions
- `simplifying_assumptions` — enables Sym.simp simplification with `MProd.fst_eq`/`MProd.snd_eq`
- `with grind` — uses `grind` to discharge VCs automatically
- Extra lemmas: `mvcgen' simplifying_assumptions with grind` + `all_goals grind [lemma1, lemma2]`

### `prove_correct?`

Use `prove_correct? methodName` to see the generated theorem statement without elaborating it (shows as "Try this:" suggestion in the IDE).

## Naming

### Hypothesis Names

All clauses support optional names that flow into proof goals:

```lean
method example (n : Nat) return (r : Nat)
  require h_pos : n > 0           -- hypothesis named h_pos
  ensures h_eq : r = n            -- goal tagged h_eq
  do
  let mut i := 0
  while' i < n
    invariant h_bound : i ≤ n     -- hypothesis named h_bound
  do i := i + 1
  return i
```

In proof goals:
- `h_pos : 0 < n` — require name
- `h_bound : i ≤ n` — invariant name
- `if_pos : i < n` / `if_neg : ¬i < n` — auto-named split conditions
- Goal tags: `vc1.h_eq`, `vc2.h_bound`, etc.

### Variable Names

Mutable variables keep their original names from the method body:
- `let mut i := 0; let mut j := 0; let mut k := 0` → variables named `i`, `j`, `k` in goals (not generic `a✝`, `b✝`)

## Internals

### InvListWithNames

Named conjunctions use `InvListWithNames` — an opaque `Prop`-valued definition that `simp` doesn't reduce. VCGen decomposes it explicitly:

```lean
noncomputable def InvListWithNames.one (name : Name) (p : Prop) : Prop := p
noncomputable def InvListWithNames.cons (name : Name) (p : Prop) (rest : Prop) : Prop := p ∧ rest
```

### MProd Splitting

When a method has ≥2 mutable variables, `do`-notation packs them into nested `MProd`. VCGen automatically splits `∀ (s : MProd A (MProd B C)), P s` into `∀ (a : A) (b : B) (c : C), P ⟨a, ⟨b, c⟩⟩` and simplifies `⟨x,y⟩.fst → x`, `⟨x,y⟩.snd → y`.

### Recursive Methods Internals

For `method_fix`:
1. `prove_correct` applies `triple_from_option_spec` + `f.partial_correctness`
2. Introduces `f_ih` (recursive call proxy) and `ih_f` (Triple-form IH)
3. `mvcgen'` finds `ih_f` as a local Triple spec for fvar-headed calls
4. Uses `tryMkBackwardRuleFromLocalSpec` (skips `mkAuxLemma`) to avoid kernel fvar issues
5. Strips `mdata` from `partial_fixpoint` recursive call markers

## Examples

### Simple (no loops)

```lean
method isEven (n : Nat) return (result : Bool)
  ensures h : result = (n % 2 == 0)
  do return n % 2 == 0

prove_correct isEven by
  mvcgen' simplifying_assumptions with grind
```

### Loop with invariants

```lean
method findSmallest (a : Array Int) return (result : Int)
  require h_ne : a.size ≠ 0
  ensures h_min : ∀ i, i < a.size → result ≤ a[i]!
  ensures h_in : ∃ i, i < a.size ∧ a[i]! = result
  do
  let mut mn := a[0]!
  let mut i : Nat := 1
  while' i < a.size
    invariant h_bound : 1 ≤ i ∧ i ≤ a.size
    invariant h_min : (∃ j, j < i ∧ a[j]! = mn) ∧ (∀ j, j < i → mn ≤ a[j]!)
  do
    if a[i]! < mn then mn := a[i]!
    i := i + 1
  return mn

prove_correct findSmallest by
  mvcgen' simplifying_assumptions with grind
```

### Recursive

```lean
method_fix gcd (a : Nat) (b : Nat) return (res : Nat)
  ensures h : res = Nat.gcd a b
  do
    if b = 0 then return a
    else
      let r ← gcd b (a % b)
      return r

prove_correct gcd by
  mvcgen' simplifying_assumptions with grind
  all_goals grind [Nat.gcd_comm, Nat.gcd_rec]
```

## File Structure

```
Loom/Test/Velvet/
  Theory.lean       -- Loop semantics, gadgets, partial-correctness specs, fixpoint bridge
  Syntax.lean       -- method, method_fix, prove_correct, while', InvListWithNames syntax
  Bench/            -- 28 benchmark case studies
Loom/Tactic/
  VCGen.lean        -- mvcgen' tactic, solve loop, emitVC, local spec handling
  Intros.lean       -- MProd splitting, InvListWithNames, introMeetPre, name hints
  Spec.lean         -- Spec lookup, backward rules, tryMkBackwardRuleFromLocalSpec
  Match.lean        -- Split rules for ite/dite/match (if_pos/if_neg naming)
```
