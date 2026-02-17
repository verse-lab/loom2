# VCGen.lean — Verification Condition Generator

## Overview

`VCGen.lean` implements a **verification condition generator (VCGen)** for monadic programs
specified via weakest preconditions (`wp`). Given a goal of the form

```
wp prog post epost s₁ … sₙ
```

the tactic `mvcgen'` repeatedly decomposes `prog` using registered `@[lspec]` spec theorems,
producing simpler **verification conditions** (VCs) that can be discharged by `grind`, `omega`,
or other proof-automation tactics.

## Background: the WP framework

### `WPMonad` (defined in `Loom/WP/Basic.lean`)

```lean
class WPMonad (m : Type u → Type v) (l : outParam (Type w)) (e : outParam (Type w))
    [Monad m] [CompleteLattice l] extends LawfulMonad m where
  wpImpl : m α → ECont l e α
  wp_pure_impl  ...   -- wp (pure x) post epost = post x          (equality)
  wp_bind_impl  ...   -- wp x (… wp (f ·) …) epost ⊑ wp (x >>= f) post epost  (one-way ⊑)
  wp_cons_impl  ...   -- monotonicity: post ⊑ post' → wp x post ⊑ wp x post'
```

Key points:

* `l` is the **lattice type** for assertions.
  For `StateT σ m` it is `σ → l'` where `l'` is the inner monad's lattice.
  For `StateM σ` (= `StateT σ Id`) it is `σ → Prop`.
* `e` is the type for error postconditions (`PUnit` when there are no exceptions).
* `wp` is defined as a `def` wrapping `WPMonad.wpImpl`.
* `wp_bind` gives **only one direction** (`⊑`, not `=`).
  The reverse cannot be proven with the current axioms; see the TODO in `Basic.lean`.

### Lattice type and "excess args"

When `l = σ₁ → σ₂ → Prop`, a goal `wp prog post epost` has type `σ₁ → σ₂ → Prop`.
In practice the goal appears **fully applied**: `wp prog post epost s₁ s₂`.
The arguments beyond the 10 base arguments of `@WPMonad.wp` are called **excess args**.
`VCGen.solve` extracts them as `args.extract 10 args.size`.

### `@[lspec]` specs

Spec theorems are registered with the `@[lspec]` attribute (`Loom/Tactic/Attr.lean`).
They can be in two forms:

| Form | Example |
|------|---------|
| **Triple** | `Triple pre prog post epost` |
| **⊑ wp** | `pre ⊑ wp prog post epost` |

`mkSpecTheorem` in `Attr.lean` processes both forms. It opens all `∀`-binders with
`forallMetaTelescopeReducing`, then extracts the **program** expression from the conclusion.
The program is indexed in a `DiscrTree` for fast lookup.

### `SymM` and maximal sharing

`SymM` is a monad extending `MetaM` that tracks **maximally shared** expressions (DAG form).
Standard MetaM functions like `mkAppN`, `mkArrow`, `mkExpectedTypeHint`, and `mkFreshExprMVar`
allocate new `Expr` nodes and **break sharing**. The Sym library provides sharing-preserving
alternatives (`mkAppS`, `instantiateRevS`, `isDefEqS`, `share`, `shareCommon`, etc.).

Sharing is critical for performance: without it, expressions grow exponentially when the
same subterm (e.g. a postcondition) appears in multiple positions.

---

## File structure

### 1. Spec lookup (`SpecTheorems.findSpecs`, lines 15–24)

```
findSpecs : SpecTheorems → Expr → MetaM (Array SpecTheorem)
```

Given a program expression `e`, looks up matching `@[lspec]` entries in the `DiscrTree`
and returns them sorted by descending priority.

### 2. Excess-arg helpers (`countExcessArgs`, `getExcessArgTypes`, lines 26–40)

Count and extract the state-argument types from a lattice type like `σ₁ → σ₂ → Prop`.

### 3. `tryMkBackwardRuleFromSpec` (lines 46–91)

**Core function.** Converts an `@[lspec]` spec into a `BackwardRule` that can be applied
to a goal.

Given a spec in `⊑` form:

```
pre ⊑ wp prog post epost          (where the lattice type is σ → Prop)
```

it produces an auxiliary lemma:

```
∀ s, pre s → wp prog post epost s
```

Steps:

1. **Instantiate** the spec theorem (`forallMetaTelescope`), creating metavariables for all
   universally quantified parameters.
2. **Match the lattice type** (`isDefEqS l l'`) — ensures the spec's lattice matches the goal's.
3. **Unify WPMonad instances** (`isDefEqGuarded instWP instWP'`) — this transitively specializes
   `m`, `e`, `cl`, and `monadInst` to the goal's concrete monad stack (e.g. `StateT Nat Id`).
4. **Create fresh metavars** for excess state args (`mkFreshExprMVar` for each `sᵢ`).
5. **Build the implication** `pre s₁ … sₙ → wp prog post epost s₁ … sₙ` using `mkArrow`
   and `mkExpectedTypeHint`. The type hint is necessary because `PartialOrder.rel` is a
   projection that `unfoldReducible`/`mkPatternFromType` cannot see through structurally.
6. **Abstract metavariables** (`abstractMVars`) and create an `mkAuxLemma` declaration.
7. **Build a `BackwardRule`** from the aux lemma (`mkBackwardRuleFromDecl`).

The result is a `BackwardRule` whose `apply` method does pattern-based unification
(via `Pattern.unify?`) against the goal, then assigns the goal metavar.

### 4. `mkBackwardRuleFromSpecs` / `mkBackwardRuleFromSpecsCached` (lines 93–154)

Iterates over candidate specs (from `findSpecs`), tries `tryMkBackwardRuleFromSpec` on each
within a fresh metavar context (`withNewMCtxDepth`), and returns the first match.

The cached version keys on `(spec decl names, instWP, excessArgs.size)` to avoid
rebuilding the same aux lemma repeatedly during a VCGen run.

### 5. `VCGenM` monad (lines 110–125)

```lean
abbrev VCGenM := ReaderT VCGen.Context (StateRefT VCGen.State SymM)
```

* **Context**: `SpecTheorems` (the `@[lspec]` database).
* **State**: backward-rule cache, collected invariant goals, collected VC goals.

### 6. `solve` (lines 170–195)

**One step of VCGen.** Given a goal `wp prog post epost s₁ … sₙ`:

1. **Parse the goal**: extract `instWP`, `l`, `monadInst`, `e` (the program), and excess args
   from the 10+ arguments of `@WPMonad.wp`.

2. **Handle `let` expressions**: if `e` is a non-dependent `let`, use `Simp.simpLet` to
   simplify it while preserving maximal sharing, then `replaceTargetDefEq`.

3. **Apply a spec**: if `e`'s head is a constant or free variable, look up matching specs
   with `findSpecs`, build/retrieve a cached backward rule, and `rule.apply goal`.
   This produces subgoals (one for each `∀`/`→` binder in the aux lemma).

4. **Fallback**: if the target isn't a `wp` application, or no spec matches, return
   an appropriate `SolveResult` variant.

### 7. `work` — the main loop (lines 219–238)

```
work : MVarId → VCGenM Unit
```

1. Preprocess the goal (`preprocessMVar`).
2. Optionally unfold `Triple` into `⊑ wp` form (`unfoldTriple`).
3. Initialize a **BFS worklist** with the goal.
4. Repeat: dequeue a goal, call `solve`.
   * On `SolveResult.goals subgoals` → enqueue all subgoals.
   * On `noProgramFoundInTarget` → emit as a VC (`emitVC`).
   * On error conditions → throw descriptive error messages.

### 8. `main` (lines 249–257)

Entry point. Runs `work` inside the `VCGenM` monad, then tags resulting invariant
and VC goals with names like `inv1`, `vc1.h`, etc.

### 9. `mvcgen'` tactic (lines 260–268)

Tactic syntax: `mvcgen'` (optionally with a simp lemma list, currently unused).
Loads the `@[lspec]` database, runs `VCGen.main` on the main goal, replaces
the main goal with the resulting invariant + VC goals.

---

## Data flow diagram

```
@[lspec] theorem spec_bind ...   ──┐
@[lspec] theorem spec_get  ...   ──┤── DiscrTree (SpecTheorems)
@[lspec] theorem spec_set  ...   ──┤
@[lspec] theorem spec_pure ...   ──┘
                                    │
                                    ▼
Goal: wp (get >>= f) post epost s
      │
      ▼
  findSpecs(get >>= f)  ──► [spec_bind]
      │
      ▼
  tryMkBackwardRuleFromSpec
      │  1. instantiate spec_bind
      │  2. unify instWP with goal's WPMonad instance
      │  3. create state metavar ?s
      │  4. build:  ∀ …, wp x (fun a => wp (f a) …) epost ?s → wp (x >>= f) post epost ?s
      │  5. abstractMVars + mkAuxLemma
      │  6. mkBackwardRuleFromDecl
      ▼
  BackwardRule
      │
      ▼
  rule.apply goal  ──►  subgoal: wp x (fun a => wp (f a) post epost) epost s
      │
      ▼
  (enqueue subgoal, repeat)
```

---

## Test section (lines 273–end)

### Unit tests

| Test | What it checks |
|------|----------------|
| Test 1 (Id, n=0) | `WPMonad.wp_bind` specializes to `Id` monad, 0 excess args |
| Test 2 (StateM Nat, n=1) | `WPMonad.wp_bind` specializes to `StateT Nat Id`, 1 excess arg |
| Test 3 (get, StateM Nat) | `spec_get_StateT` specializes correctly |

Each test synthesizes the `WPMonad` instance, calls `testBackwardRule`, and prints the
resulting aux lemma type. E.g. for Test 2:

```
∀ (α β : Type) (x : StateT Nat Id α) (f : α → StateT Nat Id β)
  (post : β → Nat → Prop) (epost : PUnit) (s : Nat),
  wp x (fun a => wp (f a) post epost) epost s → wp (x >>= f) post epost s
```

### Registered specs

| Spec | Program | Form |
|------|---------|------|
| `spec_get_StateT` | `MonadStateOf.get : StateT σ m σ` | `(fun s => post s s) ⊑ wp get post epost` |
| `spec_set_StateT` | `MonadStateOf.set x : StateT σ m PUnit` | `(fun _ => post ⟨⟩ x) ⊑ wp (set x) post epost` |
| `spec_get_StateT'` | `get : StateT σ m σ` | delegates to `spec_get_StateT` |
| `spec_set_StateT'` | `set x : StateT σ m PUnit` | delegates to `spec_set_StateT` |
| `spec_pure` | `pure a : m α` | `post a ⊑ wp (pure a) post epost` |
| `spec_bind` | `x >>= f : m β` | `wp x (fun a => wp (f a) post epost) epost ⊑ wp (x >>= f) post epost` |

Note: `spec_get_StateT'` and `spec_set_StateT'` exist because `get`/`set` elaborate to
`MonadState.get`/`MonadState.set`, a different head constant from `MonadStateOf.get`/`MonadStateOf.set`.

### Benchmark

```lean
def step (v : Nat) : StateM Nat Unit := do
  let s ← get; set (s + v); let s ← get; set (s - v)

def loop (n : Nat) : StateM Nat Unit := do
  match n with | 0 => pure () | n+1 => step n; loop n

def Goal (n : Nat) : Prop := ∀ s post (h : post s), wp (loop n) (fun _ => post) () s
```

The `solve` macro:
```lean
macro "solve" : tactic => `(tactic| {
  intro s post h
  simp only [loop, step]   -- fully unfold the program
  mvcgen' <;> grind         -- decompose with VCGen, solve VCs with grind
})
```

`solveUsingMeta` wraps this and calls `checkWithKernel` on the resulting proof term.

Typical output for `loop 400`:
```
goal_400: ~430 ms, kernel: ~18000 ms
```

The kernel check time dominates because the proof term is deeply nested — each
`spec_bind` application includes the full continuation as a lambda argument,
leading to O(n²) kernel type-inference work.

---

## Key design decisions and trade-offs

1. **Specs in `⊑` form vs `→` form.**
   Specs are stored in `⊑` form (`pre ⊑ wp prog post epost`), which is universe-polymorphic
   and works for any lattice. `tryMkBackwardRuleFromSpec` converts to `→` form at use-time
   by applying to excess state args and building `mkArrow`.
   An alternative is to store specs directly in `→` form (with explicit state args), which
   avoids `mkArrow`/`mkExpectedTypeHint` at the cost of restricting to `Prop`-based lattices.

2. **Maximal sharing via `SymM`.**
   Standard MetaM operations break expression sharing. `SymM` preserves it, which is
   essential for keeping proof terms compact. Without sharing, postconditions that appear
   in multiple subgoals would be duplicated, leading to exponential blowup.

3. **BFS worklist vs recursive descent.**
   `work` uses a BFS queue rather than recursion. This gives a flat processing order
   and avoids deep Lean call stacks for large programs.

4. **Caching backward rules.**
   The same spec (e.g. `spec_bind`) is applied many times with the same monad instance.
   The cache in `VCGen.State` avoids redundant `abstractMVars` + `mkAuxLemma` calls.

5. **`let` handling.**
   Non-dependent `let` expressions in the program are simplified via `Simp.simpLet` before
   attempting spec lookup. This preserves sharing while making the program head visible
   for `DiscrTree` matching.
