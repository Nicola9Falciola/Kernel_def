# Walking a list against indexing into it (2026-11-10)

Measured in ModularSymbolsTau and copied here on 2026-11-22. The commands are this
repository's (`scripts/techniques/`, `docs/techniques/`); every other path (`docs/bench/…`,
`docs/CFSG_EXPERIMENTS.md`, `Compute/…`, `Levels/…`, `MIGRATION_PLAN.md`, `scripts/bench/…`)
refers to that repository. Its E14 is copied in `docs/history/E14.md`.

The sixth of the technique measurements (`docs/techniques/`), on synthetic files that import
nothing (core Lean only).

## The technique

The kernel code of the certificates walks its data once, carrying a counter, and never reads an
element by its index inside a loop (the rule K5 of the old `PACKING_CORE.md`; `Compute/Pack/Walk.lean`:
"walk, don't index"). In the kernel a list is a chain of `List.cons`, so `l.getD i` walks `i` cells,
and a loop over `i` reading `l.getD i` walks the list `m` times. Where the certificates need random
access, they use a packed table: `m` slots of `w` bits in one literal, read by a shift and a mask
(`tblGet w t i = slot w t i`).

## The benchmark

`scripts/techniques/run_index_bench.py`: `m` values `v_i < 2^32` and one `decide +kernel` check of
`∑ i · v_i`. The variants differ in how `v_i` is reached:

| variant | how |
|---|---|
| `walk` (ours) | one `List.rec` over the list, carrying the position `i` |
| `sum` (control) | one `List.rec` summing the `v_i`, no position carried |
| `nth_rec` | a `Nat.rec` loop over `i`, reading `nthQ rows i`, an index in kernel form (bare `List.rec`, `Bool.rec` on `Nat.beq`) |
| `getD` | the same loop, reading `rows.getD i 0` |
| `array` | the same loop, reading `arr.getD i 0` with `arr = rows.toArray` |
| `packed` (ours, for random access) | the same loop, reading slot `i` of one literal of `m` slots of 32 bits by a shift and a mask |

A run is capped at 300 s and 24 GB, and a variant killed at one size is not run at the larger ones.

## Results

`results.jsonl`, `results.csv`, `index.png`. Kernel instructions (and time, peak memory):

| `m` | `walk` | `sum` | `packed` | `nth_rec` | `getD` | `array` |
|---:|---:|---:|---:|---:|---:|---:|
| 250 | 0.020 G | 0.018 G | 0.019 G | 2.4 G | 7.4 G | 12.4 G |
| 1000 | **0.077 G**, 0.09 GB | 0.069 G | 0.057 G | 38.7 G, 1.4 GB | 120 G, 4.9 GB | 200 G, 8.4 GB |
| 4000 | 0.32 G | 0.28 G | 0.25 G | killed: over 300 s | killed: over 24 GB | killed: over 24 GB |
| 16000 | 1.27 G | 1.10 G | 2.35 G, 0.68 GB | | | |
| 32000 | 2.84 G | | | | | |
| 40000 | **32.0 G** | | | | | |
| 64000 | **421 G**, 46 s | 4.34 G | 22.9 G, 8.9 GB | | | |

- **Indexing in a loop is quadratic, in time and in memory.** At 1000 values `List.getD` costs 1550
  times the walk (120 G against 0.077 G) and holds 4.9 GB, because the kernel keeps every
  intermediate term until the declaration is checked. At 4000 values all three indexed loops are out
  of reach: two pass 24 GB, the third 300 s. `Array` does not help: in the kernel an `Array` is a
  structure around a `List`, and `Array.getD` adds its bounds test (a `Decidable` `if`) to the same
  walk, 1.7 times `List.getD`. An index in kernel form costs a third of `List.getD`, and is still
  quadratic.
- **The packed table is the random-access alternative, and it is not free.** A read is one shift of
  a number of `32 m` bits: 57–77 k instructions a read up to 4000 slots, then growing with the table
  (147 k at 16000, 359 k at 64000), and the kernel keeps each shifted copy (8.9 GB at 64000 slots,
  2 Mbit each). The literal itself, 616 000 decimal digits at `m = 64000`, takes 192 G to
  elaborate, against 43 G for the list (the certificates load such literals in binary,
  `Compute/Loader.lean`, which avoids the decimal parse). It fits the certificates' tables (some
  thousand slots of a few bits each); it is not a substitute for a walk over a long list.
- **The walk is linear, 77–89 k a value, up to 32000 values, and then it is not.** At 40000 values it
  costs 801 k a value, at 64000 6571 k (421 G, 46 s); the memory does not change (0.72 GB). The
  control `sum`, which carries nothing, stays linear (68 k a value at 64000). This is the second
  instance of the threshold seen in `../length/`: there `List.lengthTR`, which carries an accumulator,
  turns superlinear just past `2^16`, while `List.length` and `lenN` do not. A `List.rec` whose motive
  is a function (`Nat → Nat`, to carry an argument) degrades past some length that depends on the
  step (about `2^15` here, `2^16` for `lengthTR`). Why was not investigated. The lengths of the lists
  the certificates walk with a counter were not checked against it; most are indexed by the `n`
  points of `ℙ¹(ℤ/N)` (`n ≤ 2238` in the weight-2 sweep), well below.

## Reproducing

```sh
python3 scripts/techniques/run_index_bench.py run docs/techniques/index/results.jsonl
python3 scripts/techniques/run_index_bench.py run docs/techniques/index/results.jsonl \
  20000 24000 32000 40000 48000 56000 variants=walk
sage -python scripts/techniques/run_index_bench.py plot docs/techniques/index/results.jsonl
```

About 30 minutes, most of it in the killed runs at `m = 4000`. Apple M5, 32 GB, Lean `v4.36.0-rc2`.
