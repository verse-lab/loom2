# ComplexityBench

Benchmarks for the `linearSearchArrayIdx?` variants in `Loom/Demo/Complexity.lean`.

## Build

```bash
lake build complexity-no-tick complexity-basic complexity-ghost-tuple complexity-ghost-structure complexity-ghost-state-t complexity-ghost-state-ref-t
```

## Run individually

Default input size is `10000000`.

```bash
.lake/build/bin/complexity-no-tick
.lake/build/bin/complexity-basic
.lake/build/bin/complexity-ghost-tuple
.lake/build/bin/complexity-ghost-structure
.lake/build/bin/complexity-ghost-state-t
.lake/build/bin/complexity-ghost-state-ref-t
```

Or pass an explicit input size:

```bash
.lake/build/bin/complexity-no-tick 10000000
.lake/build/bin/complexity-basic 10000000
.lake/build/bin/complexity-ghost-tuple 10000000
.lake/build/bin/complexity-ghost-structure 10000000
.lake/build/bin/complexity-ghost-state-t 10000000
.lake/build/bin/complexity-ghost-state-ref-t 10000000
```

## Benchmark with hyperfine

For a longer/more stable benchmark run, use `50000000` elements:

```bash
hyperfine --warmup 3 --runs 100 \
  '.lake/build/bin/complexity-no-tick 50000000' \
  '.lake/build/bin/complexity-basic 50000000' \
  '.lake/build/bin/complexity-ghost-tuple 50000000' \
  '.lake/build/bin/complexity-ghost-structure 50000000' \
  '.lake/build/bin/complexity-ghost-state-t 50000000' \
  '.lake/build/bin/complexity-ghost-state-ref-t 50000000'
```

For quicker runs, lower the input size and/or run count:

```bash
hyperfine --warmup 3 --runs 10 \
  '.lake/build/bin/complexity-no-tick 1000000' \
  '.lake/build/bin/complexity-basic 1000000' \
  '.lake/build/bin/complexity-ghost-tuple 1000000' \
  '.lake/build/bin/complexity-ghost-structure 1000000' \
  '.lake/build/bin/complexity-ghost-state-t 1000000' \
  '.lake/build/bin/complexity-ghost-state-ref-t 1000000'
```

## Generated C / IR

After building, the generated C is available at:

```text
.lake/build/ir/Loom/Demo/Complexity.c
```

The benchmark entrypoint C files are under:

```text
.lake/build/ir/Loom/Demo/ComplexityBench/
```
