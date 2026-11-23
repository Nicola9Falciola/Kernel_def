# `let` against inlining (2026-11-10)

Measured in ModularSymbolsTau and copied here on 2026-11-22. The commands are this
repository's (`scripts/techniques/`, `docs/techniques/`); every other path (`docs/bench/…`,
`docs/CFSG_EXPERIMENTS.md`, `Compute/…`, `Levels/…`, `MIGRATION_PLAN.md`, `scripts/bench/…`)
refers to that repository. Its E14 is copied in `docs/history/E14.md`.

The fifth of the technique measurements (`docs/techniques/`), on synthetic files that import
nothing (core Lean only).

## The technique

The kernel code of the certificates has no `let` (`CLAUDE.md`, the `decide` discipline): a value used
in a loop body is written where it is used. In the kernel a `let x := v; b` is an `Expr.letE`, which
whnf removes by substituting `v` for `x` in `b` (zeta reduction), and `(fun x => b) v` is a β-redex,
removed the same way. `have x := v; b` is a non-dependent `let` (`letE` with `nonDep`). Inlining
writes `v` at each use, so a value used `k` times appears `k` times.

## The benchmark

`scripts/techniques/run_let_bench.py`: one `decide +kernel` check of a `Nat.rec` loop of `s` steps
(`i` the index, `r` the accumulator). The step binds a value `x` computed from `i`, in four ways:
written at each use (`inline`, ours), `let`, `have`, `(fun x => …) v` (`beta`). The loop with the step
`r + 3` (30.8 k instructions a step) is subtracted.

- **`once`**: `x = i &&& 3`, used once (`r + x`).
- **`shared`**: `x = (i · i) mod 1000003`, used four times (`r + x + x · x + x`). Inlined, the value
  is written, and could be computed, four times; bound, it is written once.

## Results

`results.jsonl`, `results.csv`, `let.png`. Per step, net of the loop, at `s = 256000` (below
`s = 16000` the differences are within the noise of a few M instructions):

| | `once`: per step | against inlined | `shared`: per step | against inlined |
|---|---:|---:|---:|---:|
| inlined (ours) | **5.2 k** | 1 | **22.2 k** | 1 |
| `let x := v` | 8.4 k | +3.2 k (1.6×) | 28.5 k | +6.3 k (1.3×) |
| `have x := v` | 8.4 k | +3.2 k | 28.5 k | +6.3 k |
| `(fun x => …) v` | 9.2 k | +4.0 k | 29.4 k | +7.3 k |

- **A binding costs a substitution: 3–7 k instructions per evaluation.** That is the price of the zeta
  (or β) step, which walks the body to replace `x`. It grows with the body (3.2 k for a body with one
  use, 6.3 k for one with four), as a substitution should. `let` and `have` cost the same; the
  β-redex a little more.
- **Inlining a shared value is still cheaper**, even written four times: 22.2 k against 28.5 k. The
  four copies are the same closed term once `i` is a literal, and the kernel's whnf cache (keyed by the
  term's structure) computes it once and finds it three times. Inlining duplicates the text, not the
  work.
- **Elaboration is the same** (0.35 G for each file), and the memory nearly so (0.75 GB inlined
  against 0.81 GB bound at `s = 256000`, on 0.42 GB for the loop).

The first point agrees with E14 of `docs/CFSG_EXPERIMENTS.md`, which priced a `let` at +7.8 k per use
in a loop whose step costs 31–37 k. The second is new: it says the rule holds even where the value is
shared, as long as the copies are structurally equal. A copy that differs (another variable, a
different order of arguments) would not hit the cache, and would be computed again.

## Reproducing

```sh
python3 scripts/techniques/run_let_bench.py run docs/techniques/let/results.jsonl
sage -python scripts/techniques/run_let_bench.py plot docs/techniques/let/results.jsonl
```

About 5 minutes. Apple M5, 32 GB, Lean `v4.36.0-rc2`.
