# Branches: `if` against a raw `Bool.rec` (2026-11-10)

Measured in ModularSymbolsTau and copied here on 2026-11-22. The commands are this
repository's (`scripts/techniques/`, `docs/techniques/`); every other path (`docs/bench/…`,
`docs/CFSG_EXPERIMENTS.md`, `Compute/…`, `Levels/…`, `MIGRATION_PLAN.md`, `scripts/bench/…`)
refers to that repository. Its E14 is copied in `docs/history/E14.md`.

The fourth of the technique measurements (`docs/techniques/`), on synthetic files that import
nothing (core Lean only).

## The technique

The kernel code of the certificates branches with a raw `Bool.rec` on a `Nat.ble`/`Nat.beq` test
(`CLAUDE.md`, the `decide` discipline), never with `if`. An `if p then a else b` is
`@ite α p inst a b`: the kernel unfolds `ite` to `Decidable.casesOn`, and then reduces the instance
`inst` (`Nat.decLe x 1`, `instDecidableEqBool …`, `instDecidableAnd`) to `isTrue`/`isFalse`, which
for `Nat.decLe` goes through `Nat.ble` and a proof term. `Bool.rec a b t` needs only `t` in whnf.

## The benchmark

`scripts/techniques/run_branch_bench.py`: one `decide +kernel` check of a `Nat.rec` loop of `s` steps,
whose step `i` adds 3 or 5 to the accumulator depending on `x = i &&& 3`. Both branches are taken,
the additions are the same `Nat.add r (nat_lit 3)`, `Nat.add r (nat_lit 5)` in every variant, and the
loop without a branch (`nobranch`, 30.8 k instructions a step) is subtracted.

- **`branch`**, test `x ≤ 1`: `if x ≤ 1` (`ite_prop`), `if Nat.ble x 1 = true` (`ite_bool`),
  `bif Nat.ble x 1` (`cond`), `match Nat.ble x 1 with …` (`match`), `Bool.rec … (Nat.ble x 1)`
  (`bool_rec`, ours).
- **`and`**, test `1 ≤ x ∧ x ≤ 2`: `if 1 ≤ x ∧ x ≤ 2` (`and_ite`), one `Bool.rec` on
  `Nat.ble 1 x && Nat.ble x 2` (`and_op`), two nested `Bool.rec`s, the second test only when the
  first holds (`and_rec`, ours).

## Results

`results.jsonl`, `results.csv`, `branch.png`. Per step, net of the loop, at `s = 256000` (the same to
within 3 % from `s = 1000` on):

| one branch | instructions per step | against `Bool.rec` | kernel at `s = 256000` | memory above the loop |
|---|---:|---:|---:|---:|
| `Bool.rec` (ours) | **22.5 k** | 1 | 5.8 G | 0.14 GB |
| `match Nat.ble x 1` | 46.4 k | 2.1 | 11.9 G | 0.36 GB |
| `bif Nat.ble x 1` | 57.3 k | 2.5 | 14.7 G | 0.46 GB |
| `if x ≤ 1` | 88.5 k | 3.9 | 22.7 G | 0.72 GB |
| `if Nat.ble x 1 = true` | 137.1 k | 6.1 | 35.1 G | 1.07 GB |

| a conjunction | instructions per step | against nested `Bool.rec` |
|---|---:|---:|
| nested `Bool.rec` (ours) | **35.1 k** | 1 |
| `Bool.rec` on `… && …` | 43.9 k | 1.25 |
| `if 1 ≤ x ∧ x ≤ 2` | 159.4 k | 4.5 |

- **An `if` costs 4–6 times a `Bool.rec`**, and it is a constant per evaluation: no warm-up, no
  caching across steps (every step's test is on a different `x`). With the loop's own 31 k a step, a
  loop whose body is one test and one addition runs 2.2 times slower with `if x ≤ 1` (119 k against
  53 k a step).
- **Writing the test as a `Bool` does not help an `if`.** `if Nat.ble x 1 = true` is the most
  expensive form: the kernel reduces `instDecidableEqBool` on top of `Nat.ble`.
- **`cond` and `match` are halfway.** `bif` unfolds `cond` and then its matcher; `match` unfolds the
  generated matcher (`casesOn` behind a definition). Both still cost 2–2.5 times the bare recursor.
- **`&&` is cheap, `∧` is not.** `&&` is itself a match on `Bool`, so it adds about 9 k against the
  nested `Bool.rec`; the decidable `∧` behind an `if` adds 124 k.
- **Memory follows the work.** The kernel keeps the reduced terms until the declaration is checked:
  above the loop, the `if` forms hold 5–8 times the memory of `Bool.rec` (1.07 GB against 0.14 GB at
  `s = 256000`).

The rule of `docs/CFSG_EXPERIMENTS.md` (E14: `if r ≥ 7` costs 64 k more than `Bool.rec` on
`Nat.ble`) is confirmed: here `if x ≤ 1` costs 66 k more.

## Reproducing

```sh
python3 scripts/techniques/run_branch_bench.py run docs/techniques/branch/results.jsonl
sage -python scripts/techniques/run_branch_bench.py plot docs/techniques/branch/results.jsonl
```

About 5 minutes. Apple M5, 32 GB, Lean `v4.36.0-rc2`.
