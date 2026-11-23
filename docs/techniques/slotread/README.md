# Random access to the rows of a witness: a stack against a tree (2026-11-18)

Measured in ModularSymbolsTau and copied here on 2026-11-22. The commands are this
repository's (`scripts/techniques/`, `docs/techniques/`); every other path (`docs/bench/…`,
`docs/CFSG_EXPERIMENTS.md`, `Compute/…`, `Levels/…`, `MIGRATION_PLAN.md`, `scripts/bench/…`)
refers to that repository. Its E14 is copied in `docs/history/E14.md`.

A technique measurement (`docs/techniques/`), on synthetic files that import nothing (core
Lean only). It was prompted by the reach of the newform certificate
(`docs/bench/newform_reach/`): `Basis.lean` holds 23 GB at `N = 3001`.

## Where the memory of `Basis.lean` goes

Each kernel check of `Levels/Weight2/Level997/Basis.lean` alone in a file (baseline 0.46 GB):
`hDualPQ` peaks at 1.19 GB, `hDualMQ` at 0.73 GB, the two star checks at 0.55 GB, every other check
at the baseline. Since E12 the dual witness `Φᵀ` of a sign family is one natural, the stack `STKP`
of `n` slots of `K g` bits, and `relKillsQ` (`Compute/Pack/DualQ.lean`) reads five slots at each of
the `n` points: the point twice, and its images by `σ`, `τ`, `τ²`. A read is
`Nat.land MKs (Nat.shiftRight STK (Ks · i))`: the shift makes a copy of the stack above the slot,
half of it on average, and the kernel keeps what it evaluates until the declaration is checked
(`docs/bench/weight2_scaling/README.md`). So the check holds about `2.5 · n · |STK|`:
`2.5 · 998 · 276 KB = 0.69 GB` at `N = 997`, where 0.73 GB above the baseline is measured, and
`0.23 GB` for the `−` family (92 KB), where 0.27 GB is measured. With `|STK| ≈ n · (n / 12) · K`
bits this grows as `N³`.

## The benchmark

`scripts/techniques/run_slotread_bench.py`: `n` rows of `Ks = 27 · (n / 12)` bits (a row of `Φᵀ` at a
prime level with `n` points), two permutations `σ`, `τ` as packed tables, and rows such that
`r_c + r_{σ c} = 2 Cs` and `r_c + r_{τ c} + r_{τ² c} = 3 Cs` at every point; one `decide +kernel`
checks both relations at every point, with the five reads of `relKillsQ`. The variants differ in
where the rows are and how row `i` is read:

| variant | the rows | a read |
|---|---|---|
| `stack` (the levels, E12) | one natural of `n` slots | a shift of the stack and a mask |
| `split16` | the same stack, the points in 16 theorems | the same |
| `halve` | the same stack, nothing else | `log₂ n` halvings of the stack (a mask or a shift); the term of a half is the same at every read through it, so the kernel computes each half once and finds it again in its cache |
| `tree` | a perfect binary tree of rows (an inductive type with `leaf` and `node`) | `log₂ n` steps, one `Nat.ble` each |
| `tree4` | a perfect 4-ary tree of rows | `log₄ n` steps, two bits of `i` each |
| `list3` | three levels of lists, `∛n` each | three walks of at most `∛n` cells |
| `list2` | a list of lists, `√n` rows each | two walks of at most `√n` cells |
| `block32` | a list of 32 naturals, `n / 32` slots each | a walk of at most 32 cells, then a shift of a block |
| `nth` | a list of `n` rows | a walk of `i` cells (bare `List.rec`) |

Runs were capped at 4–5 GB (the reach ladder was running on the same machine), so the wall times
are noisy and the instructions are the measure.

## Results

`results.jsonl`, `results.csv`, `slotread.png`. Kernel instructions (billions) and peak memory:

| `n` | row bits | stack size | `stack` | `split16` | `halve` | `tree` | `tree4` | `list3` | `list2` | `nth` |
|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| 300 | 675 | 0.03 MB | 0.1 G, 0.10 GB | 0.1 G, 0.09 GB | 0.7 G, 0.10 GB | 0.8 G, 0.11 GB | 0.8 G, 0.12 GB | 1.2 G, 0.12 GB | 1.7 G, 0.14 GB | 13.7 G, 0.54 GB |
| 996 | 2241 | 0.28 MB | 1.3 G, 0.71 GB | 1.4 G, 0.14 GB | 2.8 G, 0.18 GB | 2.9 G, 0.20 GB | 2.7 G, 0.19 GB | 5.3 G, 0.27 GB | 10.1 G, 0.42 GB | killed at 4 GB |
| 1500 | 3375 | 0.63 MB | 4.6 G, 2.11 GB | 4.3 G, 0.27 GB | 4.3 G, 0.27 GB | 4.6 G, 0.27 GB | 4.8 G, 0.31 GB | 9.1 G, 0.39 GB | 18.2 G, 0.71 GB |  |
| 2004 | 4509 | 1.13 MB | 8.9 G, 4.85 GB | 10.2 G, 0.52 GB | 5.6 G, 0.34 GB | 6.2 G, 0.34 GB | 6.3 G, 0.37 GB | 13.2 G, 0.54 GB | 28.1 G, 1.05 GB |  |
| 3000 | 6750 | 2.53 MB | killed at 4 GB (9.5 GB when stopped) | 34.0 G, 1.46 GB | 9.5 G, 0.54 GB | 9.9 G, 0.53 GB | 9.3 G, 0.51 GB | 21.9 G, 0.88 GB | 50.9 G, 1.86 GB |  |
| 4002 | 8991 | 4.50 MB |  |  | 12.0 G, 0.78 GB | 13.2 G, 0.68 GB | 12.4 G, 0.68 GB | 29.5 G, 1.25 GB |  |  |
| 6000 | 13500 | 10.12 MB |  |  | 23.5 G, 1.39 GB | 21.8 G, 1.13 GB | 21.7 G, 1.24 GB | 55.0 G, 2.11 GB |  |  |
| 9000 | 20250 | 22.78 MB |  |  | 36.3 G, 2.62 GB | 40.9 G, 1.92 GB | 35.6 G, 1.86 GB | 89.1 G, 3.62 GB |  |  |

- **The stack is the fastest read below `n ≈ 1500` and the only one that is cubic.** Its memory is
  `2.5 · n · |STK|` as in the real file (0.71 GB at 996, 2.1 GB at 1500, 4.9 GB at 2004); at 3000
  it would hold about 19 GB, and the real `Basis.lean` of level 3001 holds 23.4 GB. Its
  instructions grow as fast (1.3, 4.6, 8.9 G).
- **The tree can live in the stack itself (`halve`, the owner's suggestion).** With the witness
  still one natural, `rdH` halves it `log₂ n` times; the kernel's cache, which is what makes the
  plain reads pile up, here keeps each half once: 9.5 G and 0.54 GB at 3000 points, 36 G and
  2.6 GB at 9000, the cost of the inductive tree within 15 %, for about `log₂ n` copies of the
  stack. No new type, no new data: only the read changes.
- **A tree reads a row in `log n` steps and copies nothing.** At 3000 points the binary tree costs
  9.9 G and 0.53 GB, of which about 0.2 GB is the file without the kernel; at 9000 points (a
  level near 9000) 41 G, about 4 s, and 1.9 GB. From 2004 points on it is also faster than the
  stack. Its memory follows the size of the data. The 4-ary tree is the same within 15 %.
- **Nested lists work, at twice the cost of the tree**, three levels better than two: the walks
  are short (`∛n ≤ 21`), which is not the long indexed list of `index/` (`nth`: 13.7 G for 300
  rows, out of memory at 996).
- **Splitting the theorem divides the memory and nothing else.** Sixteen theorems hold a
  sixteenth each (1.46 GB at 3000), the growth stays cubic, and so does the time (34 G at 3000).
- `block32` is left out of the table at 3000: its 32 literals of 630 000 bits take 28 s to
  elaborate from hexadecimal text, and the difference of two such runs is noise (the levels load
  their literals in binary). Up to 2004 it costs what `list3` costs.

## What it means for the certificates

Two ways to adopt it. With `halve`, the witness, the loader, the data files and the meaning of
the stack (`stackMat`, `isImg_stackMat`) stay as they are, and every `rd[Ks, MKs, stack, i]`
becomes `rdH Ks d stack i`, equal to it by a lemma:

```lean
/-- Slot `i` of `x`, a number of `2 ^ d` slots of `Ks` bits, by halving. -/
noncomputable def rdH (Ks : Nat) : Nat → Nat → Nat → Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat) (fun x _ => x)
    (fun d ih x i =>
      @Bool.rec (fun _ => Nat)
        (ih (Nat.land x (Nat.sub (Nat.shiftLeft (nat_lit 1)
          (Nat.mul Ks (Nat.shiftLeft (nat_lit 1) d))) (nat_lit 1))) i)
        (ih (Nat.shiftRight x (Nat.mul Ks (Nat.shiftLeft (nat_lit 1) d)))
          (Nat.sub i (Nat.shiftLeft (nat_lit 1) d)))
        (Nat.ble (Nat.shiftLeft (nat_lit 1) d) i))
```

With an inductive tree, the dual witness would be a tree of its `n` rows, read by a `getT` of
this form:

```lean
inductive BT where
  | leaf : Nat → BT
  | node : BT → BT → BT

/-- Row `i` of a perfect binary tree whose left subtree has `h` leaves. -/
noncomputable def getT : BT → Nat → Nat → Nat :=
  @BT.rec (fun _ => Nat → Nat → Nat) (fun a _ _ => a)
    (fun _ _ l r h i => @Bool.rec (fun _ => Nat) (l (Nat.shiftRight h (nat_lit 1)) i)
      (r (Nat.shiftRight h (nat_lit 1)) (Nat.sub i h)) (Nat.ble h i))
```

Neither is done. With the inductive tree it is not small: every reader of the stack would change (`relKillsQ`, the bound on the
digits, `rowsDualQ`, and the Hecke checks that weigh the stack at the Heilbronn images), with
their specifications, the loader (a command that builds the tree from the binary file), the
emitter and the levels. With `halve` the readers change and nothing else. This benchmark
measures the relation check only; `docs/bench/phi_tree/` measures the real checks.

## The other parts of the certificate

Does the same idea apply elsewhere? Each kernel check of the other files of level 997 alone in a
file, as for `Basis` (peak above the baseline of the file without it):

| file | checks that hold memory at 997 | the others |
|---|---|---|
| `Basis` | `hDualPQ` +0.73 GB, `hDualMQ` +0.27 GB, the two star checks +0.08 GB | at the baseline |
| `Hecke` (`docs/bench/phi_tree/`) | the full checks, `hP11` +1.24 GB down to `hP2` +0.62 GB; the one-vector checks up to +0.23 GB | at the baseline |
| `Newforms` (77 checks) | `hLin3` +0.44 GB, `hNewTable` +0.36 GB, `hTab7` +0.35 GB, `hNewDet` +0.31 GB, `hEig7` +0.12 GB, each `hMinor` +0.10 GB, `hComp7` +0.05 GB | below +0.03 GB |
| `QExp` | `hO1` +0.44 GB | `hEch` +0.04 GB |
| `Data` | `hWalk` +0.06 GB | below +0.02 GB |

Three patterns, of which the halving answers two:

1. **Reads of a slot of a big natural** (`rd[w, M, T, i]`): the dual witness in `Basis` (above)
   and in the checks of `Hecke`, and the small tables of `σ`, `τ`, `τ²`, the star and the keys of
   `ℙ¹` (`Compute/Pack/{StarQ, CuspQ, CheckQ}.lean`, `Compute/P1KeyTab.lean`), which are a few
   kilobytes at `N = 3000` and do not matter yet. `rdH` applies to all of them as it is.
2. **Walks of every slot of a wide row by repeated shifts** (`compSlots` of `companionOk`,
   `slotRes`, `modSlotsOk`, `slotsEqOk`, `unpackL`, in `Forms/Newform/Compute/`): each step copies
   the rest of the row, so a row of `w` slots costs `w / 2` copies of itself. Walked by halving
   (`sumH` of `scripts/bench/run_rowops_bench.py`) it costs `log₂ w`. On 230 rows of 126 slots of
   2500 bits, the shape of the larger orbit at `N = 2767`: 0.67 GB above the baseline by shifts,
   0.12 GB by halving. `companionOk` walks two such rows at a time.
3. **Products of a matrix of small entries with rows of big ones** (`e2StackCheck`, the
   `M_t · Ph = R` of a newform orbit): here nothing is read twice, and halving does not apply. The
   column fold `mulCols` makes four numbers of the size of the whole stack per column of `A`
   (a mask, a product, a shift, a sum) and `sumCols` three more: about `7 · k` stacks of
   `m · (d + 1) · K` bits. That is 0.08 GB for `hEig7` at 997 (0.12 measured), and 15 to 20 GB
   for the larger orbit at 2767, where `Newforms.lean` holds 23 GB (the file; its checks were not
   measured one by one there). On synthetic data at half that shape (`A` of 115 × 115 entries,
   rows of 63 slots of 1250 bits) the fold costs 20.6 G and 0.82 GB above the baseline, and one
   dot product per row of `A`, which multiplies each small entry by a row, 1.4 G and 0.31 GB:
   **15 times fewer instructions and 2.6 times less memory**. The fold was designed for short
   rows of small entries (E2), and a newform orbit has rows of tens of kilobytes.

`rowops.jsonl` holds the rows of items 2 and 3 (the kernel instructions of the walks at the
larger size are lost in 50 s of elaboration of the hexadecimal literals; their memory is not).

## How to reproduce

    python3 scripts/techniques/run_slotread_bench.py run OUT.jsonl [n ...] [variants=v,v]
    sage -python scripts/techniques/run_slotread_bench.py plot OUT.jsonl
    python3 scripts/bench/run_rowops_bench.py OUT.jsonl walk:230:126:2500:seq walk:230:126:2500:halve \
      prod:115:63:1250:stack prod:115:63:1250:rows

`n` must be a multiple of 6. `run_rowops_bench.py`, the rows of `rowops.jsonl`, was not ported:
it stays in ModularSymbolsTau, under `scripts/bench/`. Apple M5, 32 GB, Lean `v4.36.0-rc2`.
