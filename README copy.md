# velvet-simple

A Lean 4 framework for formal program verification using weakest precondition (WP) semantics and Hoare logic.

## Overview

Velvet-Simple provides tools for formally proving correctness of imperative programs by:
- Defining pre/post-conditions and loop invariants
- Generating verification conditions automatically via the `SymM` monad
- Using monad algebra to model program semantics

## Project Structure

```
velvet-simple/
├── VelvetSimple.lean          # Main library entry point
├── Main.lean                  # Executable entry point
├── add_sub_cancel.lean        # Example: verified add/subtract cancellation
│
├── VelvetSimple/
│   ├── Defs.lean              # Mathematical foundations: complete lattices,
│   │                          # continuation monad, monad algebras (MAlg, MAlgOrdered, etc.)
│   ├── Basic.lean             # WP theorems, Hoare triple rules, loop verification
│   │
│   ├── Velvet/                # Core verification framework
│   │   ├── Syntax.lean        # DSL syntax: while, for, invariants, method definitions
│   │   ├── Tactic'.lean       # VC generator in SymM monad (key file)
│   │   ├── Theory.lean        # WP rules for VelvetM operations
│   │   ├── Attr.lean          # Custom attributes for velvetSpec theorems
│   │   └── Extension.lean     # Lean extension for spec storage
│   │
│   ├── Instances/             # Monad algebra instances
│   │   ├── Basic.lean         # Id monad, DivM monad, Prop lattice
│   │   ├── StateT.lean        # State monad transformer
│   │   ├── ReaderT.lean       # Reader monad transformer
│   │   ├── ExceptT.lean       # Exception monad transformer
│   │   └── Gen.lean           # Generator/choice monad
│   │
│   └── Tests/                 # Verification test cases
│       ├── Bind.lean          # Bind operation tests
│       ├── ContolFlow.lean    # Control flow pattern tests
│       └── ControlFlowBind.lean # Combined tests
│
└── bench/                     # Performance benchmarks
    ├── Bench.lean             # Benchmark harness (key file for perf testing)
    ├── run_bench.sh           # Script to run benchmarks
    ├── compare.py             # Compare results between runs
    ├── visualize.py           # Generate visualizations
    ├── results.json           # Latest benchmark results
    └── result.pdf             # Visualization output
```

## Key Files

### `VelvetSimple/Velvet/Tactic'.lean`
The core VC generator implemented in `SymM` monad. Contains:
- `vcGenSym` - worklist-based VC generation loop
- `vcGenStepSym` - single step: applies velvetSpec theorems or simplifies
- `velvetVCGenSym'` - main entry point for VC generation
- `velvet_vcgen'` - tactic for invoking VC generation

### `bench/Bench.lean`
Performance test harness with synthetic benchmarks:
- **sqrt**: Square root with loop invariant
- **addSubCancel**: N iterations of add/subtract (linear chain)
- **loopAddSub**: Nested loops with variable unrolling

Use this to measure performance impact of changes to the VC generator.

## Architecture

The framework is layered:
1. **Math foundations** (`Defs.lean`) - Complete lattices, continuation monads
2. **Generic WP framework** (`Basic.lean`) - Monad-independent theorems
3. **Monad instances** (`Instances/`) - DivM, StateT, ExceptT
4. **DSL syntax** (`Syntax.lean`) - Lean macros for imperative constructs
5. **VC generation** (`Tactic'.lean`) - Automated verification condition generation

