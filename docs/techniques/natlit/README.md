# `nat_lit` against `OfNat` numerals (2026-11-10)

Measured in ModularSymbolsTau and copied here on 2026-11-22. The commands are this
repository's (`scripts/techniques/`, `docs/techniques/`); every other path (`docs/bench/…`,
`docs/CFSG_EXPERIMENTS.md`, `Compute/…`, `Levels/…`, `MIGRATION_PLAN.md`, `scripts/bench/…`)
refers to that repository. Its E14 is copied in `docs/history/E14.md`.

The second of the technique measurements (`docs/techniques/`), on synthetic files that import
nothing (core Lean only).

## The technique

A numeral `123 : ℕ` elaborates to `@OfNat.ofNat ℕ 123 (instOfNatNat 123)`: the elaborator synthesizes
an instance for it, and the kernel unfolds `instOfNatNat` to reach the literal. `nat_lit 123` is the
raw literal `Expr.lit (.natVal 123)`, with nothing to synthesize or unfold. The certificates write
their constants and data as `nat_lit` in `noncomputable def`s (`CLAUDE.md`, the `decide` discipline;
the big data now come from `#load_nat`/`#load_list`, which build the same raw literals).

## The benchmark

`scripts/techniques/run_natlit_bench.py`, measured by `scripts/techniques/technique_bench.py`: each file in full
and without the kernel (`-Ddebug.skipKernelTC=true`), against an empty file. Kernel = full − no
kernel; elaboration = no kernel − empty file.

- **`data`**: `m` 576-bit literals in one `List ℕ`, and a `decide +kernel` check of their sum
  (a bare `List.rec` of `Nat.add`). The 2 × 2 of how the literals are written (`OfNat` numeral or
  `nat_lit`) and how the list is defined (`def`, which is compiled, or `noncomputable def`).
- **`loop`**: a `Nat.rec` loop of `s` steps, each adding the constant `3` or `nat_lit 3`.

## Results

`results.jsonl`, `results.csv`, `natlit.png`. The data, `m = 16384` (2.9 MB of source):

| | elaboration | | kernel | peak memory |
|---|---:|---:|---:|---:|
| `OfNat`, `def` | 147 G | 7.2 s | 1.2 G | 0.66 GB |
| `OfNat`, `noncomputable def` | 111 G | 5.2 s | 1.5 G | 0.50 GB |
| `nat_lit`, `def` | 86 G | 4.0 s | 1.1 G | 0.43 GB |
| `nat_lit`, `noncomputable def` (ours) | **54 G** | **2.2 s** | 0.9 G | **0.28 GB** |

At `m = 65536` (12 MB) only ours goes through with the default options: 214 G, 8.8 s, 0.87 GB.
Both `OfNat` variants stop at the default `maxHeartbeats` (200000, in `whnf`), and `nat_lit` in a
compiled `def` reaches `maxRecDepth` in the compiler.

- **It is the elaboration, not the kernel.** Writing the literals as `nat_lit` halves the
  elaboration (111 → 54 G) and its memory (0.50 → 0.28 GB). Not compiling the definition saves
  another 25–35 %. Together that is a factor 2.7 against a plain `def` of numerals, and the only
  combination that scales to 65536 literals. The cost grows linearly with `m` in all four.
- **In the kernel it is noise.** The data's kernel cost is 0.9–1.5 G at `m = 16384`, with no
  consistent order between the variants at the sizes measured. The kernel unfolds each
  `instOfNatNat v` once, which is cheap next to the arithmetic on 576-bit numbers.
- **A constant in a loop costs nothing either way.** `Nat.add r 3` and `Nat.add r (nat_lit 3)` in a
  `Nat.rec` of 256000 steps: 7.92 G against 7.89 G (0.4 %). The `OfNat` term is the same at every
  step, and the kernel reduces it once and caches it. This agrees with E14 of
  `docs/CFSG_EXPERIMENTS.md` (+0.1–0.25 k instructions a use, under 1 %).

So `nat_lit` matters where literals are many and distinct, as in the data of a level, and there it
matters for elaboration. Inside the kernel code of `Compute/` it is a matter of style. Since the
loader (`Compute/Loader.lean`) builds the data's literals directly, the elaboration gain on the data
is now taken by the loader, which also skips the parser.

## Reproducing

```sh
python3 scripts/techniques/run_natlit_bench.py run docs/techniques/natlit/results.jsonl
sage -python scripts/techniques/run_natlit_bench.py plot docs/techniques/natlit/results.jsonl
```

About 5 minutes. Apple M5, 32 GB, Lean `v4.36.0-rc2`.
