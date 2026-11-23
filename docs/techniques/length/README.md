# The length of a list: `List.length` against `lenN` (2026-11-10)

Measured in ModularSymbolsTau and copied here on 2026-11-22. The commands are this
repository's (`scripts/techniques/`, `docs/techniques/`); every other path (`docs/bench/…`,
`docs/CFSG_EXPERIMENTS.md`, `Compute/…`, `Levels/…`, `MIGRATION_PLAN.md`, `scripts/bench/…`)
refers to that repository. Its E14 is copied in `docs/history/E14.md`.

The third of the technique measurements (`docs/techniques/`), on synthetic files that import
nothing (core Lean only).

## The technique

Core's `List.length` is defined by structural recursion,
`| cons _ as => HAdd.hAdd (length as) 1`: the equation compiler turns it into `List.brecOn`, which
the kernel unfolds with its `below` bookkeeping at every element, and each `+ 1` goes through the
`HAdd`/`Add` instance chain. Ours, `lenN` (`Compute/Pack/Walk.lean`, proved equal to `List.length` by
`lenN_eq`), is a bare `List.rec` with `Nat.add ih (nat_lit 1)`. The certificates use `lenN` for every
length they check.

## The benchmark

`scripts/techniques/run_length_bench.py`: the list `[0, 1, …, m − 1]` of raw `nat_lit`s and one
`decide +kernel` check `Nat.beq (len rows) m = true`. The cost of the data (a check `Nat.beq m m`
with the same list, `base`) is subtracted. Six variants of `len`:

| variant | definition |
|---|---|
| `length` | core's `List.length`: structural recursion, `HAdd` |
| `lengthTR` | core's `List.lengthTR`: structural recursion on an accumulator, `Nat.succ` |
| `struct_natadd` | structural recursion, `Nat.add … (nat_lit 1)` |
| `rec_hadd` | a bare `List.rec`, `ih + 1` (`HAdd`) |
| `lenN` | ours: a bare `List.rec`, `Nat.add ih (nat_lit 1)` |

`struct_natadd` and `rec_hadd` each change one of the two differences between `length` and `lenN`.
The files set `maxRecDepth 1000000` and `maxHeartbeats 0`, so that the list literal itself elaborates
at 256000 elements (14 s), and each run is capped at 600 s (`TIME_LIMIT_S`).

## Results

`results.jsonl`, `results.csv`, `length.png`. Kernel instructions net of the data:

| | per element | `m = 64000` | `m = 256000` | against `lenN` |
|---|---:|---:|---:|---:|
| `List.length` | 222 k | 14.2 G, 0.94 s | 56.8 G, 4.1 s | 3.7 |
| `List.lengthTR` | 214 k up to `2^16`, then superlinear | 13.7 G, 0.71 s | **killed after 600 s** | |
| structural recursion, `Nat.add` | 184 k | 11.8 G | 46.0 G | 3.0 |
| `List.rec`, `ih + 1` | 85 k | 5.4 G | 20.6 G | 1.4 |
| `lenN` (ours) | **61 k** | **3.9 G, 0.11 s** | **15.5 G, 0.16 s** | 1 |

- **`lenN` costs 3.7 times less than `List.length`**, at every length from 1000 to 256000: 61 k
  against 222 k instructions per element. It also holds less memory: above the data, 0.63 GB against
  2.0 GB at `m = 256000`.
- **Most of it is the recursion.** Structural recursion alone (with `Nat.add`) costs 3.0 times the
  bare recursor; the `HAdd` instance alone (on the bare recursor) adds 40 %. The two compose to the
  3.7 of `List.length`.
- **`List.lengthTR` breaks down past `2^16` elements.** It costs what `List.length` costs up to
  `m = 64000`, then the excess over its linear cost grows about as `(m − 65536)²`:

  | `m` | 64000 | 72000 | 80000 | 88000 | 96000 | 112000 | 128000 | 256000 |
  |---|---:|---:|---:|---:|---:|---:|---:|---:|
  | kernel | 13.7 G | 24.6 G | 56.8 G | 121 G | 229 G | 615 G | 1304 G, 160 s | over 600 s |

  An earlier run at `m = 256000` was stopped after 72 minutes. The memory stays normal (2 GB at
  `m = 128000`), and elaboration is unaffected (the run without the kernel takes 19 s). `lengthTR`
  differs from `length` in carrying the count as an accumulator `Nat.succ (Nat.succ …)`; why the
  kernel slows down past `2^16` was not investigated. None of the other variants shows it up to
  256000.

## Reproducing

```sh
TIME_LIMIT_S=600 python3 scripts/techniques/run_length_bench.py run docs/techniques/length/results.jsonl
sage -python scripts/techniques/run_length_bench.py plot docs/techniques/length/results.jsonl
```

The points of `lengthTR` between 64000 and 128000 (and their `base`) were added by hand, with
`measure(source(m, v))` from the same script. About 30 minutes, 10 of them for `lengthTR` at
`m = 256000`. Apple M5, 32 GB, Lean `v4.36.0-rc2`.
