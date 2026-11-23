# The length of a list: `List.length` against the compiler's kernel form (2026-11-23)

What the compiler's kernel form of `List.length` buys against the native function, in the kernel.
Measured in this repository on Lean `v4.37.0-rc1`.

## The technique

Core's `List.length` is defined by structural recursion,
`| cons _ as => HAdd.hAdd (length as) 1`: the equation compiler turns it into `List.brecOn`, which
the kernel unfolds with its `below` bookkeeping at every element, and each `+ 1` goes through the
`HAdd`/`Add` instance chain. `KernelDef/ListForms.lean` gives it a kernel form, `listLength`, a bare
`List.rec` with `Nat.add ih (nat_lit 1)`, and the rule `length_eq_listLength`: a `kernel_def` whose
source calls `l.length` gets `KernelDef.listLength l` in its kernel form.

## The benchmark

`scripts/techniques/run_length_bench.py`: the list `[0, 1, …, m − 1]` of raw `nat_lit`s and one
`decide +kernel` check `Nat.beq (len rows) m = true`, under `#count_heartbeats`. The cost of the data
(a check `Nat.beq m m` with the same list, `base`) is subtracted. The variants of `len`:

| variant | definition |
|---|---|
| `kernel_def` | a `kernel_def` whose source is `l.length`: its kernel form is `KernelDef.listLength l` |
| `length` | core's `List.length`: structural recursion, `HAdd` |
| `lengthTR` | core's `List.lengthTR`: structural recursion on an accumulator, `Nat.succ` |
| `struct_natadd` | structural recursion, `Nat.add … (nat_lit 1)` |
| `rec_hadd` | a bare `List.rec`, `ih + 1` (`HAdd`) |
| `lenN` | hand-written: a bare `List.rec`, `Nat.add ih (nat_lit 1)` |

`struct_natadd` and `rec_hadd` each change one of the two differences between `length` and `lenN`.

- Every file imports `KernelDef` and defines every function, so every variant pays the same imports
  and the same definitions and differs only in its check; the run without the kernel
  (`-Ddebug.skipKernelTC=true`) cancels them.
- Every file runs three times in full and three times without the kernel, and the minimum of each
  figure is kept (`REPEATS`): with these imports single runs spread by up to 0.5 G, as much as the
  kernel's work below 16000 elements.
- `hb` is the heartbeats of the check, in thousands, the same at every run; below, net of `base`.
- The files set `maxRecDepth 1000000` and `maxHeartbeats 0`, so that the list literal elaborates at
  256000 elements; each run is capped by `TIME_LIMIT_S`.

## Results

`results.jsonl`, `results.csv`, `length.png`. Kernel instructions net of the data, in billions:

| `m` | `kernel_def` (`listLength`) | `List.length` | `lenN` | `List.rec`, `ih + 1` | structural recursion, `Nat.add` | `List.lengthTR` |
|---:|---:|---:|---:|---:|---:|---:|
| 256 | 0.017 | 0.050 | 0.012 | 0.015 | 0.040 | 0.042 |
| 1000 | 0.058 | 0.165 | 0.048 | 0.070 | 0.138 | 0.168 |
| 4000 | 0.198 | 0.689 | 0.206 | 0.283 | 0.577 | 0.648 |
| 16000 | 0.837 | 2.800 | 0.849 | 1.147 | 2.320 | 2.655 |
| 64000 | 3.351 | 11.269 | 3.411 | 4.527 | 9.307 | 10.585 |
| 128000 | 6.707 | 22.403 | 6.769 | 9.026 | 18.609 | 21.205 |
| 256000 | 13.433 | 44.881 | 13.578 | 18.305 | 37.198 | 42.429 |

`List.lengthTR` also at 72000 (11.97 G), 80000 (13.26), 88000 (14.58), 96000 (15.90) and 112000
(18.49): 165 to 166 k an element at every size.

`kernel_def` against `List.length`, per element, the ratio, and the peak memory above the data:

| `m` | `kernel_def`, k instr. | `List.length`, k instr. | ratio | `kernel_def`, k heartbeats | `List.length`, k heartbeats | ratio | peak, GB |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 256 | 67.2 | 193.4 | 2.88 | 19 | 70 | 3.68 | 0.001 / 0.002 |
| 1000 | 57.8 | 165.1 | 2.86 | 73 | 269 | 3.68 | 0.002 / 0.007 |
| 4000 | 49.4 | 172.2 | 3.49 | 290 | 1070 | 3.69 | 0.008 / 0.033 |
| 16000 | 52.3 | 175.0 | 3.35 | 1158 | 4275 | 3.69 | 0.033 / 0.130 |
| 64000 | 52.4 | 176.1 | 3.36 | 4632 | 17097 | 3.69 | 0.124 / 0.509 |
| 128000 | 52.4 | 175.0 | 3.34 | 9264 | 34193 | 3.69 | 0.249 / 1.023 |
| 256000 | 52.5 | 175.3 | 3.34 | 18528 | 68387 | 3.69 | 0.500 / 2.044 |

(The heartbeats are of the whole list, in thousands, not per element.)

- The compiler's form costs 3.34 to 3.36 times less than `List.length` in kernel instructions from
  16000 elements on (52.4 k against 175 k an element), and 3.69 times less in heartbeats at every
  size. Below 4000 elements the kernel's work (under 0.17 G) is within the spread of the runs:
  there the heartbeats are the figure. The bench pair `bench/Length.lean` gives the same: 3.35 in
  instructions, 3.69 in heartbeats (`docs/library_forms/README.md`).
- `kernel_def` is `lenN`: the same heartbeats at every size (the two terms are equal up to the type
  of the elements), and instructions within 2 % from 16000 elements on.
- Most of the gain is the recursion: structural recursion alone (with `Nat.add`) costs 2.74 times
  the bare recursor, the `HAdd` instance alone (on the bare recursor) 1.34 times.
- `List.lengthTR` is linear, 165 to 166 k an element up to 256000 (42.4 G, 2.8 s), 6 % below
  `List.length`.
- Memory above the data at 256000 elements: 0.50 GB against 2.04 GB. Kernel time there: 0.45 s
  against 3.4 s; the machine was indexing files during the run, so the times are rough, and
  instructions are the measure.
- Importing Mathlib changes nothing for this check: with `import Mathlib` beside
  `import KernelDef`, `List.length` at 16000 elements costs the kernel 2.795 G against 2.800 G, and
  4275 thousand heartbeats in both. `List.length` is core's constant either way. Measured once,
  outside the rows.

## Reproducing

Build first, since the files import `KernelDef`:

```sh
lake build KernelDef
TIME_LIMIT_S=600 python3 scripts/techniques/run_length_bench.py run docs/techniques/length/results.jsonl
sage -python scripts/techniques/run_length_bench.py plot docs/techniques/length/results.jsonl
```

About 17 minutes (`REPEATS=3`), no run near the time limit. The plot writes `results.csv` and
`length.png` next to `results.jsonl`. Apple M5, 32 GB, Lean `v4.37.0-rc1`.
