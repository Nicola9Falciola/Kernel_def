> The record of the experiment in ModularSymbolsTau, copied on 2026-11-22 from its
> `docs/bench/kernel_form/README.md` (working tree at commit `64248e8`). Its paths
> (`ModularSymbolsTau/…`, `Compute/…`, `Levels/…`, `scripts/bench/kernel_form/…`, `docs/…`) and
> its commits refer to that repository, not to this one. The data files it names (`*.jsonl`,
> `reach_step2.json`) are copied beside it; the snapshots `snapshot_364e70a/`,
> `snapshot_unmarked/` and `snapshot_swarOk/` stayed there. The compiler it describes is
> `KernelDef/KernelForm.lean` here, and its list forms `KernelDef/ListForms.lean`.

# Kernel forms compiled from readable definitions (2026-11-21)

The experiment behind `ModularSymbolsTau/Compute/KernelForm.lean`, and the gates of the three
steps of its use in the tree. Scripts and Lean files: `scripts/bench/kernel_form/`. Rows:
`results.jsonl` (the prototype), `results_superseded.jsonl` (its faulty rows, each with its
reason), `level_cost.jsonl` (steps 1 to 3, before and after), `results_tree.jsonl` (checks of
the prototype measured again in the tree after step 1), `peak_997_hecke.jsonl` (the peak of one
file, looked into), `results_step2.jsonl` and `reach_step2.json` (step 2), `results_step3.jsonl`
(step 3). `snapshot_364e70a/` holds the terms of the 114 marked definitions at commit `364e70a`,
`snapshot_unmarked/` those of the 21 definitions of step 3 before it.

## The question

The definitions the kernel evaluates in a certificate are written by hand in the form the
playbook asks for (`docs/CFSG_EXPERIMENTS.md`, E6 to E9 and E14): bare recursors, `Nat.*` heads,
raw literals, `Bool.rec` on `Nat.ble` and `Nat.beq`, no `let`. 114 definitions of the core carry
the mark `-- [Kernel_Optimized]` or `-- TODO [Kernel_Optimized]`. They are hard to read, and
each has lemmas that restate a recursor step so that a proof can use it.

Can a definition be written in ordinary notation, and the kernel form be produced from it, with
an equation the kernel checks, at no cost to the certificates?

## The answer

Yes, on everything tried.

- `kernel_def f …` is written as a `def`. It gives `f`, the kernel form; `Src.f`, the readable
  definition (an ordinary `def`); and `f.eq_src : f xs = Src.f xs`, proved by a term the compiler
  builds and the kernel checks. The equations of `Src.f` are restated on `f` under the names Lean
  reserves (`f.eq_1 …`, `f.eq_def`), so `rw [f]`, `simp [f]` and `unfold f` read the kernel form
  as the readable definition.
- The 32 marked definitions of `Compute/Pack/Walk.lean` at commit `364e70a`, written readably,
  all compile, and every equation is proved by the compiler: 14 by unfolding, 12 by rewriting
  with the equations of earlier definitions, 6 by an induction the compiler writes. Of the 9
  tagged ones, 8 give the hand-written term and `rdH` gives it up to η of the outer `fun`. Of the
  23 marked `TODO`, 11 are identical, 3 identical up to the form of numerals, 9 different.
- 21 more definitions (the chains of `dualStackH`, `checkPkH`, `checkOneH`, `qlen`) give the
  hand-written terms. Real checks of levels 997 and 3511 on forms compiled from readable sources
  cost what the hand-written ones cost, within the noise of the meter.
- The 9 forms that differ are cheaper: three checks of weight 4 at level 37 cost 16 to 27 %
  fewer kernel instructions, with the same peak.
- Of three further reductions tried, one was already there, one gains nothing that matters, and
  one (a read specialised to the level) gains 22 to 34 % on the dual check and 2 % where the time
  is. None is in the compiler.

## Method

- The checks are real ones: a theorem of a level, alone in a file with the preamble of its part
  (imports, data, definitions), as `scripts/bench/run_basis_heavy_bench.py theorems` does. Level
  997 of weight 2 and level 37 of weight 4 are in the repository; level 3511 is a prime level in
  minimal mode, emitted outside it (`scripts/bench/run_newform_reach.py` with `LEVELS_OUT`) and
  read through `KERNEL_FORM_LEVELS`.
- `lean -j1 -DElab.async=false`, the file in full and with `-Ddebug.skipKernelTC=true`. Every
  file runs 3 times in full and 2 times without the kernel (5 and 3 where the table says so) and
  the minimum of each is kept. The kernel's instructions are the difference; the peak is that of
  the full run. `hb` is the count of small allocations of the first copy, in thousands
  (`#count_heartbeats in`), which does not vary from run to run.
- The variants of a theorem:
  - `hand`: verbatim, on the hand-written forms;
  - `kc`: its heads replaced by the same checks compiled from readable sources (`DualKC.lean`,
    `CheckKC.lean`, on top of `WalkKC.lean`);
  - `gen*`: the whole statement, heads and arguments, on copies of the core's definitions in
    which every hand-written form of `Walk.lean` is replaced by the generated one (`rebase% gen`,
    `KC/Rebase.lean`);
  - `ctl*`: the same on copies of the hand-written forms themselves, the control: it differs from
    `gen*` only in the terms of the forms of `Walk.lean`;
  - `gen`, `ctl`: the heads only replaced by their copies (`kernel_rebase`).
- Apple M5, 32 GB, Lean `v4.36.0-rc2`. The machine was shared with a second agent, one heavy job
  at a time.

Two traps, both met.

- The noise of the meter. The preamble of `Basis` at 997 alone, ten runs: 24.41 to 26.08 G
  (`bench.py noise 997 Basis`). A check of 1 G cannot be compared in one copy, so a theorem is
  stated `copies` times in its file, and the kernel's work is multiplied while the rest is not.
- A copy with the same statement is not checked again. `decide +kernel` proves a statement
  through an auxiliary lemma it finds again by the statement, so forty copies of a theorem cost
  one. Copy `i` therefore states `Nat.beq i i = true ∧ …`. A second form of the same trap: when
  only the heads of a bundle are replaced by copies, two conjuncts that shared a computation by
  naming the same term no longer do (the control of `hHecke` costs 34.4 G with its heads copied
  and 31.1 G with the whole statement copied). Hence `gen*` and `ctl*`.

## Coverage

`python3 scripts/bench/kernel_form/build.py`, then `build.py tests`: `tests/Coverage.lean`
compares every generated `KC.f` with the hand-written `Compute.Pack.f` (`Cov.lean`), ignoring
metadata.

| definition | mark | generated term against the hand-written one | equation by |
|---|---|---|---|
| `lenN` | tag | identical | induction |
| `rdH` | tag | identical up to η | induction |
| `rdL` | tag | identical | rewriting |
| `absFields`, `colsFieldsLt`, `colsFieldsIn` | tag | identical | induction |
| `normsLe`, `shapePk`, `suppPk` | tag | identical | rewriting |
| `PN.val`, `PN.add`, `PN.beq`, `PN.sub`, `PN.mul`, `PN.bias`, `readPN`, `rowsCheck` | TODO | identical | unfolding |
| `weighPk`, `weighPkPN`, `weighPkSlot` | TODO | identical | rewriting |
| `PN.modN` | TODO | identical up to numerals | unfolding |
| `packPN`, `packPk` | TODO | identical up to numerals | rewriting |
| `PN.smul`, `PN.ofInt`, `smulSlot` | TODO | different: `Int.rec` where the hand form calls a matcher | unfolding |
| `weighPN`, `weighSlot` | TODO | different: `List.rec` for `List.foldr` | rewriting |
| `stackPN` | TODO | different: `List.rec` for `List.map` | rewriting |
| `fitsPN` | TODO | different: `Bool.rec` for `&&` | unfolding |
| `addField` | TODO | different: the `let` written out, `Bool.rec` for `bif` | unfolding |
| `weighFields` | TODO | different: `Nat.rec` with the carried argument, for `brecOn` | induction |

The hand-written `rdH` has two binders for five arguments; the compiler never η-reduces. The 23
marked `TODO` keep their pairs and their `Int`: the compiler changes control flow, not
representation.

`tests/CoverageDual.lean` and `tests/CoverageCheck.lean` do the same for the 21 others
(`onesD`, `swarW`, `relKillsH`, `slotWH`, `rowsDualH`, `dualStackH`; `qdigits`, `qrow`, `qsteps`,
`qlen`, `dropN`, `sumSlH`, `allFitH`, `innerH`, `wPH`, `wQH`, `cmpH`, `checkPkH`, `oPH`, `oQH`,
`checkOneH`): all identical. `Lemmas.lean` proves seven statements of `Walk.lean` on the generated
forms from the readable equations, with no lemma that restates a recursor step.
`tests/Axioms.lean`: the generated theorems of the compiled definitions rest on `propext` and
`Quot.sound` only. `tests/Rejects.lean`: well-founded recursion and a recursive call that is not
on a field of the constructor matched are rejected, with nothing added. `tests/Faults.lean`: a
`kernel_def` whose readable definition has an error adds nothing.

Compile cost of the prototype (`lean -j1`): `WalkKC.lean`, 32 definitions, 19.51 G and 2.6 s,
against 15.9 to 16.6 G for its imports alone.

## Identical terms cost the same

`runs.sh` (`bench.py thm 997 Basis hDualPQ dualStackH variants=hand,kc copies=40`, and so on;
`REPEATS=3 SKIP_REPEATS=2 KCIMPORT=CheckKC HB=1`). Kernel G, peak GB, `hb`.

| check | `hand` | `kc` |
|---|---|---|
| 997 `hDualPQ` × 40 | 39.947, 0.498, 1172 | 40.046, 0.499, 1171 |
| 997 `hPs13_163` × 4 | 47.328, 0.853, 14868 | 47.163, 0.856, 14895 |
| 997 `hP3` × 16 | 28.956, 0.543, 2242 | 29.097, 0.539, 2241 |
| 997 `hShVQ` × 300 | 16.572, 0.473, 83 | 16.524, 0.474, 83 |
| 3511 `hDualPQ` × 1 (5 full runs) | 4.776, 0.711, 5063 | 4.888, 0.715, 5062 |
| 3511 `hPs3_7` × 1 (2 full runs) | 0.162, 0.467, 309 | 0.141, 0.462, 306 |

The differences at 997 are −0.4 to +0.5 %, inside the spread of the runs of one file (0.1 to
1.1 G). At 3511 the runs of one file fall in two groups 1.5 G apart, so one copy says little
there beyond the peak and the allocation count. The rows tagged `rev` are a second run of two of
these measurements, made in the review of the prototype on a separate build of its modules
(997 `hDualPQ` × 40: 39.982 and 40.051; weight 4 `hDualP` × 30: 39.711, `gen*` 30.582, `ctl*`
39.765).

## The forms that differ are cheaper

Weight 4, level 37 (`runs.sh`: `bench.py thm 37 Hecke hHecke k=4 'variants=hand,gen*,ctl*'
copies=8`, and so on). Kernel G, peak GB, `hb`.

| check | `hand` | `gen*` | `ctl*` | `gen*` against `hand` |
|---|---|---|---|---|
| `hDualP` × 30 | 39.591, 0.521, 1548 | 30.444, 0.499, 1191 | 38.740, 0.532, 1582 | −23 % |
| `hRankR` × 30 | 38.778, 0.523, 1442 | 28.440, 0.525, 1007 | 37.705, 0.547, 1476 | −27 % |
| `hHecke` × 8 | 30.793, 0.619, 4981 | 26.009, 0.592, 4275 | 31.076, 0.639, 5095 | −16 % |

These three checks reach seven of the nine forms that differ (`tests/Reach.lean`); `PN.ofInt` and
`weighPN` are reached by none of them.

## Three reductions tried

- Equal subterms merged. Already there: Lean shares every `def` it elaborates maximally, and the
  compiler does the same to its output.
- `a < b` as `Nat.ble (Nat.succ a) b` in place of `Nat.blt a b` (the rows tagged `ble` and
  `bigble`). `hShVQ` × 300: 16.524 to 15.245 G, −7.7 %. Elsewhere nothing measurable: `hDualPQ`
  40.046 to 39.971, `hPs13_163` 47.163 to 47.798, `hP3` 29.097 to 29.876. The shape check costs
  0.055 G at 997, so this gains nothing that matters. The option that produced these rows
  (`kernelForm.blt`) is not in the compiler of the tree: the rows cannot be run again as they
  were.
- A check specialised to the literals of a level: the recursion of `rdH` on the depth unfolded
  for the level, shifts and thresholds as literals, written by `spec.py` and not by the compiler
  (`runs.sh`: `bench.py files 997 Basis hDualPQ_spec $(spec.py 997 hDualPQ copies=40)`).

  | check | general (`kc`) | one definition a depth | depths nested as closed `fun`s |
  |---|---|---|---|
  | 997 `hDualPQ` × 40 | 40.641 G, 0.505 GB, hb 1171 | 31.833, 0.498, 874 (−22 %) | 26.954, 0.515, 746 (−34 %) |
  | 3511 `hDualPQ` × 1 | 4.746, 0.724, 5062 | 3.883, 0.685, 3864 | 3.284, 0.758, 3233 |
  | 997 `hPs13_163` × 4 | 48.788, 0.873, 14895 | 47.792, 0.843, 14680 (−2 %) | not run |

  The nested form is written out as text, `2^d` copies: its file elaborates 5.6 G more at 997 and
  27 G more at 3511, which eats the gain. The equation with the general form is checked by the
  kernel alone (`kernel_rfl%`, `KC/KernelRfl.lean`): the specialised read equals
  `rdL 2214 MKs 7` for every stack and index (`tests/SpecEq.lean`), and the whole specialised
  dual check equals `dualStackH` at those literals for every value of the other arguments
  (`tests/SpecCheckEq.lean`: 18.19 G for the file against 16.0 G for its imports). With the
  number of points a literal as well (`n = 998`) the kernel did not finish (stopped after 150 s
  at 7.35 GB): only the parameters of the read may be literals in the equation. The dual checks
  are about 2 G of the 58 G of level 997, and the one-vector checks, where the time is, gain
  2 %, so the specialiser was not built into the compiler.

## What was superseded, and why

`results_superseded.jsonl`; no figure above comes from it.

- The first version of the meter (rows with `exp: thm`, tags `first` and `r3`): one copy of a
  theorem, its preamble subtracted, single runs. The figures are inside the noise (the shape
  check `hShBQ`, which costs about 0.05 G, reads 2.1, 2.2 and −1.4 G in its three variants).
- Copies with the same statement (tags `c20`, `c3`, and the first `w4` rows): the kernel checked
  one copy (`hDualPQ` × 20 reads 0.8 to 2.1 G where forty copies cost 40 G).
- Runs that failed, and were run again: a slip in the template of the copies, an ambiguous name
  in a specialised file, a `Decidable` instance not found in another. Paths of the scratch folder
  in their error texts are written `<work>`.
- Level 3511 with two full runs (tag `big`): the runs of one file there fall in two groups 1.5 G
  apart, and the two variants fell in different groups. Tag `big5` has five.

## To run it again

The comparison is with the hand-written forms, so it runs in a tree at commit `364e70a` to which
`ModularSymbolsTau/Compute/KernelForm.lean` has been added and built; `runs.sh` holds the
commands, in the order of this file. `build.py` compiles the Lean files of
`scripts/bench/kernel_form/` (they are outside the libraries of the project) into
`KERNEL_FORM_WORK/lib`; `bench.py` writes its scratch files and its rows under `KERNEL_FORM_WORK`.
The rows of `results.jsonl` were measured with the prototype of the compiler, in a scratch folder.
The compiler of the tree differs from it in what follows, none of which changes a term the
sources of this folder give: the options `kernelForm.eta` and `kernelForm.blt`, `kernel_rfl%`
and `kernel_form … from …` are gone; an error of the readable definition adds nothing; an
attribute written on a `kernel_def` goes to the kernel form; a numeral of `ℕ` becomes a raw
literal also under a metadata node.

The Lean files of the folder were compiled with the compiler of the tree in the tree after step 1
(`build.py`, `build.py tests`), where the comparison of `tests/Coverage.lean` is empty (both
sides are generated) and those of `tests/CoverageDual.lean` and `tests/CoverageCheck.lean` were
still against hand-written forms: all identical. After step 2 they compile and run as well, and
every comparison is of a generated form with a generated form. The whole of `runs.sh` was not
run again at commit `364e70a`.

## Step 1 in the tree

The compiler is `ModularSymbolsTau/Compute/KernelForm.lean`, and the 45 marked definitions of
`Compute/Pack/Prim.lean` (6), `Compute/Pack/Encode.lean` (6), `Compute/PackedMul.lean` (1) and
`Compute/Pack/Walk.lean` (32) are `kernel_def`s, under their names and with their arguments in
their order. `Levels/` was not regenerated: the core builds without a warning, and levels 23 and
997 of weight 2 (with their `Newforms`) and level 37 of weights 4 and 6 build as they are. The
terms and the costs below were recorded at commit `364e70a` before the first edit.

### The term gate

`python3 scripts/bench/kernel_form/term_gate.py compare docs/bench/kernel_form/snapshot_364e70a`.
`snapshot_364e70a/` holds the type and the value of each of the 114 marked definitions at commit
`364e70a`, in a canonical form (constants by name, universe levels, literals, de Bruijn indices;
no binder name, no metadata). A tagged definition must be identical, or identical up to η; six
tagged definitions whose hand-written terms held `OfNat` numerals are accepted with raw literals.

| file | definition | mark | against the term of `364e70a` |
|---|---|---|---|
| `Prim` | `slot`, `sumN` | tag | identical |
| `Prim` | `pow2`, `mask`, `unsalt`, `bitAt` | tag | identical up to numerals (accepted) |
| `Encode` | `fieldCol`, `spCount`, `spFields`, `tblGet` | tag | identical |
| `Encode` | `fieldNeg`, `fieldMag` | tag | identical up to numerals (accepted) |
| `PackedMul` | `packNat` | tag | identical |
| `Walk` | `lenN`, `rdL`, `absFields`, `colsFieldsLt`, `colsFieldsIn`, `normsLe`, `shapePk`, `suppPk` | tag | identical |
| `Walk` | `rdH` | tag | identical up to η |
| `Walk` | `PN.val`, `PN.add`, `PN.beq`, `PN.sub`, `PN.mul`, `PN.bias`, `readPN`, `rowsCheck`, `weighPk`, `weighPkPN`, `weighPkSlot` | TODO | identical |
| `Walk` | `PN.modN`, `packPN`, `packPk` | TODO | identical up to numerals |
| `Walk` | `PN.smul`, `PN.ofInt`, `smulSlot` | TODO | different: `Int.rec` for the matcher `PN.smul.match_1` |
| `Walk` | `weighPN`, `weighSlot` | TODO | different: `List.rec` for `List.foldr` |
| `Walk` | `stackPN` | TODO | different: `List.rec` for `List.map` |
| `Walk` | `fitsPN` | TODO | different: `Bool.rec` for `Bool.and` |
| `Walk` | `addField` | TODO | different: the `let` written out, `Bool.rec` for `cond` |
| `Walk` | `weighFields` | TODO | different: `Nat.rec` for `Nat.brecOn` |

The 69 marked definitions of the other files are identical: they were not touched.

### The cost gate

`python3 scripts/bench/kernel_form/level_cost.py levels docs/bench/kernel_form/level_cost.jsonl
TAG 2:997` with `REPEATS=3 SKIP_REPEATS=2`, then `… TAG 4:37 6:37 2:23` with
`REPEATS=5 SKIP_REPEATS=3`; `TAG` is `before` at commit `364e70a` and `after` in the migrated
tree; `level_cost.py report docs/bench/kernel_form/level_cost.jsonl before after` prints the
table. Every part of a level in place, in full and without the kernel. Kernel G is the difference
of two minima, each good to a few tenths of a G (the full runs of one file differ by up to 1.4 G);
the full G is the steadier figure.

| part | kernel G before | after | full G before | after | peak GB before | after |
|---|---:|---:|---:|---:|---:|---:|
| weight 2, 997, `Data` | 5.739 | 4.915 | 29.441 | 28.686 | 0.508 | 0.508 |
| weight 2, 997, `Basis` | 7.714 | 7.717 | 34.211 | 34.296 | 0.536 | 0.542 |
| weight 2, 997, `Hecke` | 32.411 | 32.415 | 70.177 | 70.243 | 0.838 | 0.861 |
| weight 2, 997, `QExp` | 4.522 | 4.560 | 36.577 | 36.712 | 0.667 | 0.668 |
| weight 2, 997, `Newforms` | 79.574 | 79.746 | 127.149 | 127.417 | 0.963 | 0.966 |
| weight 4, 37, `Data` | 0.200 | 0.208 | 23.799 | 23.886 | 0.447 | 0.447 |
| weight 4, 37, `Basis` | 8.600 | 6.933 | 33.047 | 31.455 | 0.533 | 0.527 |
| weight 4, 37, `Hecke` | 5.484 | 4.827 | 34.612 | 34.049 | 0.575 | 0.555 |
| weight 4, 37, `QExp` | 0.292 | 0.293 | 28.370 | 28.439 | 0.504 | 0.504 |
| weight 6, 37, `Data` | 0.203 | 0.198 | 23.805 | 23.886 | 0.446 | 0.447 |
| weight 6, 37, `Basis` | 27.435 | 21.859 | 52.128 | 46.623 | 0.718 | 0.682 |
| weight 6, 37, `Hecke` | 12.826 | 11.225 | 42.921 | 41.394 | 0.869 | 0.813 |
| weight 6, 37, `QExp` | 0.370 | 0.371 | 28.503 | 28.591 | 0.505 | 0.506 |
| weight 2, 23, `Data` | 0.139 | 0.136 | 23.724 | 23.809 | 0.446 | 0.446 |
| weight 2, 23, `Basis` | 0.182 | 0.159 | 24.821 | 24.901 | 0.452 | 0.452 |
| weight 2, 23, `Hecke` | 0.603 | 0.636 | 26.933 | 27.022 | 0.461 | 0.461 |
| weight 2, 23, `QExp` | 0.154 | −0.023 | 27.809 | 27.742 | 0.502 | 0.503 |
| weight 2, 23, `Newforms` | 0.676 | 0.679 | 30.980 | 31.079 | 0.522 | 0.523 |

The instructions of weight 2 are the same within the noise: the kernel figures of 997 move by
0.003 to 0.17 G but for `Data` (−0.82 G, whose three full runs before read 29.44, 30.00, 30.00
and after 29.51, 29.07, 28.69). A file without the kernel costs 0.06 to 0.11 G more than before,
at every level: what it imports is larger (the compiler, the readable definitions, their
equations). Weights 4 and 6 are cheaper where the forms that differ are evaluated: `Basis` −19 %
and −20 %, `Hecke` −12 % and −12 %, with a lower peak.

One figure is worse beyond the noise: the peak of `Hecke` at 997, 0.02 GB more
(`peak_997_hecke.jsonl`; `peak_probe.py`). Run by run (the table keeps the minimum), the file
peaks at 0.839 to 0.847 GB at the sources of `364e70a` (six runs) and at 0.858 to 0.866 in the
migrated tree (five), for the same instructions, and at 0.494 without the kernel in both. No
definition is behind it:

- with the nine files exactly as at `364e70a` and one line added, the import of the compiler in
  `Prim.lean`, the file peaks at 0.858 to 0.862: every term is the old one and the peak is the
  new one (the levels import `Lean` already, through `Compute/Loader.lean`: what their imports
  gain is the module of the compiler);
- in the migrated tree with `pow2` and `mask` written by hand as before it peaks at 0.858 to
  0.862, and with `rdH` written by hand (the η-reduced form) at 0.856 to 0.863;
- each check alone allocates and peaks as before: `hPs13_163`, the heaviest, `hb` 14868 and
  0.852 GB in four copies (0.853 at `364e70a`), 0.834 alone;
- the file cut after that group peaks at 0.840, as the whole file did before
  (`peak_probe.py cut 997`). The 0.02 GB come after it, in the recursion checks `hStepQ<p>`,
  which need 0.12 GB at most each when 0.38 GB have just been freed;
- a file with the group and those checks only (`peak_probe.py copies 997 hPs13_163`) peaks at
  one of three values, 0.834, 0.851 or 0.859, the same at every run of one file, and which one
  changes with things that change no term: the checks stated on copies of their definitions, or
  the name under which the bench module is imported (two runs of the same five files: 0.834,
  0.859, 0.859, 0.859, 0.859, then 0.851, 0.859, 0.851, 0.834, 0.834).

So it is a matter of how the memory freed by one declaration is reused by the next, which the
new import moves, and not of what a check needs. It was looked for on this one file; the other
parts of the four levels read within 0.006 GB of before, or lower.

### The checks of the prototype, in the migrated tree

`results_tree.jsonl`: rows of `runs.sh` measured again with the scripts of this folder in the
migrated tree, where `hand` is what the tree now holds. Full G (the steadier figure), peak GB,
`hb`.

| check | `hand`, in the tree | other variants, in the tree | `hand` at `364e70a` |
|---|---|---|---|
| 997 `hDualPQ` × 40 | 69.359, 0.498, 1172 | `kc` 69.272, 0.499, 1171 | 69.170, 0.498, 1172 |
| 997 `hPs13_163` × 4 | 79.344, 0.852, 14868 | `kc` 79.517, 0.855, 14895 | 78.712, 0.853, 14868 |
| 997 `hP3` × 16 | 56.526, 0.552, 2242 | `kc` 56.477, 0.539, 2241 | 55.084, 0.543, 2242 |
| weight 4, 37, `hDualP` × 30 | 55.589, 0.520, 1174 | `gen*` 55.902, `ctl*` 55.782 | 64.340, 0.521, 1548 |
| weight 4, 37, `hHecke` × 8 | 52.458, 0.577, 4202 | `gen*` 52.659, `ctl*` 52.634 | 56.896, 0.619, 4981 |

The checks of weight 2 allocate what they allocated, to the unit of `hb`. The checks of weight 4
cost in the tree what `gen*` cost in the prototype (55.492 and 52.267), and the three variants
now agree, as they must: the tree holds the generated forms.

### The cost of compiling the files

`REPEATS=5 python3 scripts/bench/kernel_form/level_cost.py files … TAG` on the four files: the
file in full, the loading of its imports included, minimum of five runs.

| file | marked | full G before | after | wall s before | after | peak GB before | after |
|---|---:|---:|---:|---:|---:|---:|---:|
| `Compute/Pack/Prim.lean` | 6 | 11.267 | 13.863 | 1.49 | 1.99 | 0.208 | 0.253 |
| `Compute/Pack/Encode.lean` | 6 | 16.077 | 18.688 | 2.03 | 2.54 | 0.257 | 0.320 |
| `Compute/PackedMul.lean` | 1 | 17.699 | 20.309 | 2.14 | 2.66 | 0.267 | 0.329 |
| `Compute/Pack/Walk.lean` | 32 | 31.676 | 36.539 | 3.18 | 3.77 | 0.306 | 0.375 |

The first three cost 2.6 G more each, with 6, 6 and 1 definitions. Most of it is the import of
the compiler, which is `import Lean`: a file that holds the two imports of `Prim.lean` alone
costs 10.9 G, and 13.3 G with the compiler or with `import Lean` added (0.206 and 0.250 GB).
`Walk.lean` costs 4.9 G more, so its 32 definitions and the proofs changed cost about 2.3 G.

## Step 2 in the tree

The other 69 marked definitions are `kernel_def`s, in the 22 files of the table below, under their
names and with their arguments in their order: all 114 marked definitions are now `kernel_def`s,
and none is `noncomputable`. `Levels/` was not regenerated: the core builds without a warning, and
levels 23 and 997 of weight 2 (with their `Newforms`), level 37 of weights 4 and 6, and the
composite level 39 of weight 2 build as they are. The compiler imports the five modules of Lean
it uses in place of `import Lean`.

### The term gate

`python3 scripts/bench/kernel_form/term_gate.py compare docs/bench/kernel_form/snapshot_364e70a`:
exit 0 on all 114 (77 identical, 6 up to η, 15 up to numerals, 16 different, all 16 marked `TODO`).
The 69 of this step:

| file | definition | mark | against the term of `364e70a` |
|---|---|---|---|
| `Compute/P1Key` | `radixAt` | tag | identical up to numerals (accepted) |
| `Compute/P1KeyTab` | `tabKey` | tag | identical |
| `Compute/P1KeyTab` | `tabSlot` | tag | identical up to numerals (accepted) |
| `Compute/Pack/Points` | `crossEqNat`, `ptC`, `ptD`, `rowPtOk` | tag | identical |
| `Compute/Pack/Weight` | `blkIdx` | tag | identical up to numerals (accepted) |
| `Compute/Pack/Quotient` | `qdigits`, `qrow`, `qsteps`, `qlen` | tag | identical |
| `Compute/Pack/DualQ` | `relKillsQ`, `slotWQ`, `rowsDualQ`, `relKillsH`, `slotWH`, `rowsDualH` | tag | identical |
| `Compute/Pack/StackQ` | `onesD`, `swarW`, `dualStackQ`, `dualStackH` | tag | identical |
| `Compute/Pack/CheckQ` | `wP`, `wQ`, `dropN`, `sumSlH`, `allFitH`, `innerH`, `wPH`, `wQH`, `cmpH`, `checkPkH`, `oPH`, `oQH`, `checkOneH` | tag | identical |
| `Compute/Pack/CuspQ` | `bdWQ`, `cuspCheckSQ` | tag | identical |
| `Compute/Pack/StarQ` | `tgtWQ` | tag | identical |
| `Compute/Pack/FamQ` | `dsOk` | tag | identical |
| `Compute/PackedDense` | `rowEq` | tag | identical |
| `Compute/PackedDense` | `dotH`, `slotSumH`, `rowsEq` | tag | identical up to η |
| `Compute/PackedColumnQ` | `stepLevelsQ`, `eqNatsQ` | tag | identical |
| `Forms/Newform/Compute/Checks` | `companionH` | tag | identical |
| `Forms/Newform/Compute/Checks` | `compSlotsH`, `compRowsH` | tag | identical up to η |
| `Cert/Acceptance/Level11` | `accVP`, `accWP`, `accΦTP`, `accVM`, `accWM`, `accΦTM`, `accYB`, `accSelB`, `accColT`, `accPosT`, `accPhi` | tag | identical |
| `Cert/Acceptance/Level11` | `accCol` | tag | identical up to numerals (accepted) |
| `Forms/QExpBasis/Acceptance/Level11` | `accLT` | tag | identical up to numerals (accepted) |
| `Compute/Pack/HeckeKey` | `rowModN` | TODO | identical up to numerals |
| `Compute/Pack/HeckeKey` | `heckeRowsOn` | TODO | different: `Nat.rec` for `Nat.brecOn` |
| `Compute/Pack/HeckeKeyW` | `heckeRowsOnW` | TODO | different: `Nat.rec` for `Nat.brecOn` |
| `Compute/Pack/HeckeImg` | `checkPk` | TODO | different: `Bool.rec` for `Bool.and`, `List.rec` for `List.all` |
| `Compute/Pack/PlusImg` | `rankBCheckS` | TODO | different: `Bool.rec` for `Bool.and`, `List.rec` for `List.all` and `List.map` |
| `Compute/Pack/PlusImgW` | `dualCheckW`, `rankCheckW` | TODO | different: `Bool.rec` for `Bool.and`, `List.rec` for `List.all` and `List.map` |
| `Cert/Model/Cusps` | `cuspListOk` | TODO | different: `Bool.rec` for `Bool.and`, `Bool.or`, `Bool.not` |

The five up to η are the hand-written forms with fewer binders than arguments. The numerals
accepted in tagged definitions are `e - 1` in `radixAt`, `12` and `4096` in `tabSlot`, `w + 1` in
`blkIdx`, and the entries of the lists `accCol` and `accLT` (`NUMERALS_OK` in `term_gate.py`).

### The cost gate

`level_cost.py levels … after2 2:997` (`REPEATS=3 SKIP_REPEATS=2`), then `… after2 4:37 6:37 2:23`
(`REPEATS=5 SKIP_REPEATS=3`), against the rows `before` (commit `364e70a`) and `after` (step 1).

| part | kernel G at `364e70a` | step 1 | step 2 | full G at `364e70a` | step 1 | step 2 | peak GB at `364e70a` | step 1 | step 2 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| weight 2, 997, `Data` | 5.739 | 4.915 | 4.886 | 29.441 | 28.686 | 29.116 | 0.508 | 0.508 | 0.508 |
| weight 2, 997, `Basis` | 7.714 | 7.717 | 7.702 | 34.211 | 34.296 | 34.733 | 0.536 | 0.542 | 0.539 |
| weight 2, 997, `Hecke` | 32.411 | 32.415 | 32.210 | 70.177 | 70.243 | 70.484 | 0.838 | 0.861 | 0.856 |
| weight 2, 997, `QExp` | 4.522 | 4.560 | 4.578 | 36.577 | 36.712 | 37.269 | 0.667 | 0.668 | 0.668 |
| weight 2, 997, `Newforms` | 79.574 | 79.746 | 79.992 | 127.149 | 127.417 | 128.270 | 0.963 | 0.966 | 0.967 |
| weight 4, 37, `Data` | 0.200 | 0.208 | 0.192 | 23.799 | 23.886 | 24.332 | 0.447 | 0.447 | 0.447 |
| weight 4, 37, `Basis` | 8.600 | 6.933 | 6.850 | 33.047 | 31.455 | 32.404 | 0.533 | 0.527 | 0.490 |
| weight 4, 37, `Hecke` | 5.484 | 4.827 | 4.711 | 34.612 | 34.049 | 34.392 | 0.575 | 0.555 | 0.551 |
| weight 4, 37, `QExp` | 0.292 | 0.293 | 0.295 | 28.370 | 28.439 | 28.981 | 0.504 | 0.504 | 0.504 |
| weight 6, 37, `Data` | 0.203 | 0.198 | 0.193 | 23.805 | 23.886 | 24.340 | 0.446 | 0.447 | 0.447 |
| weight 6, 37, `Basis` | 27.435 | 21.859 | 21.672 | 52.128 | 46.623 | 46.904 | 0.718 | 0.682 | 0.675 |
| weight 6, 37, `Hecke` | 12.826 | 11.225 | 10.987 | 42.921 | 41.394 | 41.627 | 0.869 | 0.813 | 0.805 |
| weight 6, 37, `QExp` | 0.370 | 0.371 | 0.372 | 28.503 | 28.591 | 29.112 | 0.505 | 0.506 | 0.506 |
| weight 2, 23, `Data` | 0.139 | 0.136 | 0.133 | 23.724 | 23.809 | 24.258 | 0.446 | 0.446 | 0.446 |
| weight 2, 23, `Basis` | 0.182 | 0.159 | 0.172 | 24.821 | 24.901 | 25.349 | 0.452 | 0.452 | 0.452 |
| weight 2, 23, `Hecke` | 0.603 | 0.636 | 0.219 | 26.933 | 27.022 | 27.471 | 0.461 | 0.461 | 0.461 |
| weight 2, 23, `QExp` | 0.154 | -0.023 | 0.137 | 27.809 | 27.742 | 28.422 | 0.502 | 0.503 | 0.503 |
| weight 2, 23, `Newforms` | 0.676 | 0.679 | 0.681 | 30.980 | 31.079 | 31.621 | 0.522 | 0.523 | 0.523 |

The kernel figures of step 2 are those of step 1 or lower, and so are the peaks (a minimum over
the runs: the five runs of `Basis` of weight 4 read 0.490, 0.500, 0.499, 0.499, 0.499). The full
figures of step 2 are 0.45 G above those of step 1 in every file alike, the smallest included.
That is the meter and not the tree. The full runs of one file fall in modes about 0.45 G apart
(`Hecke` at 997 read 71.06, 70.67, 70.18 at `364e70a`), and the low one was not seen again after
the batch of step 1: the sources of `364e70a` themselves, built and measured again later, read
70.61 to 70.72 for that file. The checks of the next table were measured before and after step 2
within the hour: without the kernel, twelve of their fifteen files cost 0.06 to 0.08 G more after
(the three others moved by 0.7 to 1.3 G, one way or the other: the modes again), which is what
the 69 readable definitions and their equations add to the imports.

### The checks that reach the definitions marked TODO

`scripts/bench/kernel_form/todo_rows.sh TAG` (`results_step2.jsonl`, tags `before2` and
`after2`): the checks of the measured levels whose statement reaches one of the eight `TODO`
definitions of this step, in copies, in the tree before the first edit of step 2 and after it.
`hList` (`Data`) reaches `cuspListOk`; `hRankB` reaches `rankBCheckS` in weight 2 and `rankCheckW`
above; `hP2` reaches `rowModN` and `heckeRowsOn`; `hRankR` reaches `rankCheckW`; `hDualP` and
`hDualM` reach `dualCheckW`; `hHecke` reaches `checkPk`, `rowModN` and `heckeRowsOnW`.

| check | `hb` before | after | kernel G before | after | full G before | after | peak GB before | after |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| weight 2, 997, `hList` × 100 | 29 | 28 | 0.607 | 0.532 | 26.436 | 26.435 | 0.453 | 0.452 |
| weight 2, 997, `hRankB` × 100 | 59 | 57 | -0.726 | 0.487 | 29.311 | 29.235 | 0.462 | 0.461 |
| weight 2, 997, `hP2` × 12 | 2949 | 2713 | 28.003 | 27.444 | 55.553 | 53.659 | 0.541 | 0.542 |
| weight 2, 39, `hList` × 100 | 39 | 34 | 1.392 | 1.022 | 27.123 | 26.817 | 0.453 | 0.452 |
| weight 2, 39, `hRankB` × 100 | 65 | 62 | 1.007 | 0.800 | 28.060 | 27.920 | 0.458 | 0.458 |
| weight 2, 39, `hP2` × 30 | 221 | 209 | 3.460 | 3.158 | 29.065 | 28.835 | 0.457 | 0.457 |
| weight 4, 37, `hList` × 100 | 29 | 28 | 0.594 | 0.521 | 26.307 | 26.308 | 0.452 | 0.452 |
| weight 4, 37, `hRankB` × 100 | 65 | 63 | 0.914 | 0.754 | 28.143 | 28.065 | 0.459 | 0.459 |
| weight 4, 37, `hRankR` × 30 | 970 | 927 | 27.091 | 25.324 | 52.676 | 51.643 | 0.531 | 0.535 |
| weight 4, 37, `hDualP` × 30 | 1174 | 1132 | 30.447 | 29.339 | 55.632 | 54.606 | 0.520 | 0.490 |
| weight 4, 37, `hDualM` × 30 | 1167 | 1124 | 30.207 | 29.120 | 55.390 | 54.380 | 0.520 | 0.490 |
| weight 4, 37, `hHecke` × 8 | 4202 | 4037 | 25.959 | 24.808 | 52.499 | 51.417 | 0.578 | 0.572 |
| weight 6, 37, `hRankR` × 12 | 2248 | 2176 | 27.919 | 27.179 | 53.154 | 52.487 | 0.587 | 0.584 |
| weight 6, 37, `hDualP` × 12 | 2701 | 2631 | 29.701 | 28.994 | 54.502 | 53.870 | 0.551 | 0.548 |
| weight 6, 37, `hHecke` × 4 | 10677 | 10403 | 35.409 | 34.441 | 61.802 | 60.894 | 0.811 | 0.802 |

Every check allocates less, and every check above 1 G costs less. Three of them were measured at
`364e70a` in the prototype, so that the three states can be read together, in kernel G and `hb`:
`hDualP` × 30, 39.591 and 1548, then 30.447 and 1174 after step 1, then 29.339 and 1132;
`hRankR` × 30, 38.778 and 1442, then 27.091 and 970, then 25.324 and 927; `hHecke` × 8, 30.793
and 4981, then 25.959 and 4202, then 24.808 and 4037.

### Which measured part reaches which definition

`reach_step2.json` (`build.py run scripts/bench/kernel_form/tests/ReachLevels.lean`): for each
of the 69, the parts of the five levels above that hold a theorem whose statement reaches it
through the definitions of the project.

- No part: the 13 acceptance data (`acc…`: the levels do not import them); `wP`, `wQ`,
  `relKillsQ`, `slotWQ`, `rowsDualQ`, `dualStackQ` (the levels state the halving forms);
  `compSlotsH`, `compRowsH`, `companionH` (the `Newforms` in the repository state `companionOk`).
- `Data` of every level: `cuspListOk`, `crossEqNat`, `rowPtOk`; with `Hecke`: `radixAt`; with
  `Hecke`, `QExp` and `Newforms`: `ptC`, `ptD`.
- `Basis` of weight 2: `bdWQ`, `cuspCheckSQ`, `relKillsH`, `slotWH`, `rowsDualH`, `rankBCheckS`,
  `onesD`, `swarW`, `dualStackH`, `tgtWQ`; `Basis` of every weight: `dsOk`; `Basis` of weights 4
  and 6: `dualCheckW`, `rankCheckW`, `blkIdx`.
- `Hecke` of weight 2: `dropN`, `sumSlH`, `allFitH`, `innerH`, `wPH`, `wQH`, `cmpH`, `checkPkH`,
  `oPH`, `oQH`, `checkOneH`, `heckeRowsOn`, `qdigits`, `qrow`, `qsteps`, `qlen`, `stepLevelsQ`,
  `eqNatsQ`; at the prime levels 23 and 997 also `tabSlot`, `tabKey`; `Hecke` of weights 4 and 6:
  `checkPk`, `heckeRowsOnW`; `Hecke` of every weight: `rowModN`.
- `QExp` of weight 2 and `Newforms`: `dotH`, `slotSumH`, `rowEq`, `rowsEq`.

### The cost of compiling the files

`REPEATS=3 python3 scripts/bench/kernel_form/level_cost.py files … TAG`: the file in full, the
loading of its imports included. Before is commit `364e70a` for the four files of step 1 (tag
`before`) and the tree after step 1 for the others (tag `before2`); after is tag `after2`.

| file | marked | full G before | after | wall s before | after | peak GB before | after | before is |
|---|---:|---:|---:|---:|---:|---:|---:|---|
| `Compute/P1Key.lean` | 1 | 18.644 | 18.790 | 2.48 | 2.52 | 0.316 | 0.317 | the tree after step 1 |
| `Compute/P1KeyTab.lean` | 2 | 17.144 | 17.347 | 2.39 | 2.42 | 0.307 | 0.308 | the tree after step 1 |
| `Compute/Pack/Points.lean` | 4 | 19.502 | 17.294 | 2.81 | 2.43 | 0.364 | 0.308 | the tree after step 1 |
| `Compute/Pack/PlusImg.lean` | 1 | 19.216 | 16.950 | 2.53 | 2.15 | 0.327 | 0.266 | the tree after step 1 |
| `Compute/Pack/Weight.lean` | 1 | 24.246 | 21.924 | 2.89 | 2.48 | 0.337 | 0.277 | the tree after step 1 |
| `Compute/Pack/HeckeKey.lean` | 2 | 21.193 | 19.116 | 2.95 | 2.56 | 0.369 | 0.313 | the tree after step 1 |
| `Compute/Pack/HeckeKeyW.lean` | 1 | 29.759 | 27.592 | 3.53 | 3.13 | 0.391 | 0.334 | the tree after step 1 |
| `Compute/Pack/HeckeImg.lean` | 1 | 19.404 | 17.170 | 2.56 | 2.14 | 0.325 | 0.265 | the tree after step 1 |
| `Compute/Pack/PlusImgW.lean` | 2 | 21.020 | 18.870 | 2.67 | 2.28 | 0.335 | 0.275 | the tree after step 1 |
| `Compute/Pack/Quotient.lean` | 4 | 20.684 | 18.636 | 2.89 | 2.51 | 0.370 | 0.313 | the tree after step 1 |
| `Compute/Pack/DualQ.lean` | 6 | 19.485 | 17.329 | 2.54 | 2.15 | 0.330 | 0.269 | the tree after step 1 |
| `Compute/Pack/StackQ.lean` | 4 | 19.838 | 17.796 | 2.57 | 2.17 | 0.327 | 0.267 | the tree after step 1 |
| `Compute/Pack/CheckQ.lean` | 13 | 27.322 | 25.753 | 3.30 | 3.01 | 0.392 | 0.336 | the tree after step 1 |
| `Compute/Pack/CuspQ.lean` | 2 | 19.451 | 17.674 | 2.78 | 2.40 | 0.362 | 0.306 | the tree after step 1 |
| `Compute/Pack/StarQ.lean` | 1 | 20.934 | 18.892 | 2.63 | 2.23 | 0.335 | 0.275 | the tree after step 1 |
| `Compute/Pack/FamQ.lean` | 1 | 18.448 | 16.289 | 2.50 | 2.10 | 0.323 | 0.264 | the tree after step 1 |
| `Compute/PackedDense.lean` | 4 | 24.573 | 23.030 | 2.93 | 2.57 | 0.338 | 0.280 | the tree after step 1 |
| `Compute/PackedColumnQ.lean` | 2 | 17.217 | 15.522 | 2.44 | 2.06 | 0.320 | 0.262 | the tree after step 1 |
| `Forms/Newform/Compute/Checks.lean` | 3 | 27.445 | 25.694 | 3.31 | 2.97 | 0.377 | 0.322 | the tree after step 1 |
| `Cert/Model/Cusps.lean` | 1 | 31.403 | 29.373 | 4.05 | 3.70 | 0.457 | 0.422 | the tree after step 1 |
| `Cert/Acceptance/Level11.lean` | 12 | 34.269 | 32.335 | 4.28 | 3.89 | 0.473 | 0.442 | the tree after step 1 |
| `Forms/QExpBasis/Acceptance/Level11.lean` | 1 | 30.085 | 27.896 | 4.30 | 3.90 | 0.513 | 0.476 | the tree after step 1 |
| `Compute/KernelForm.lean` |  | 17.454 | 13.669 | 2.09 | 1.34 | 0.248 | 0.149 | the tree after step 1 |
| `Compute/Pack/Prim.lean` | 6 | 11.267 | 11.785 | 1.49 | 1.57 | 0.208 | 0.210 | `364e70a` |
| `Compute/Pack/Encode.lean` | 6 | 16.077 | 16.563 | 2.03 | 2.12 | 0.257 | 0.260 | `364e70a` |
| `Compute/PackedMul.lean` | 1 | 17.699 | 18.182 | 2.14 | 2.25 | 0.267 | 0.268 | `364e70a` |
| `Compute/Pack/Walk.lean` | 32 | 31.676 | 34.529 | 3.18 | 3.39 | 0.306 | 0.317 | `364e70a` |

The files of step 2 cost 1.6 to 2.3 G less than before it, though they compile more (but
`P1Key.lean` and `P1KeyTab.lean`, which now import the compiler: 0.15 and 0.20 G more): with the
imports the compiler uses (`Lean.Elab.Command`, `Lean.Elab.PreDefinition.Basic`,
`Lean.Compiler.CSimpAttr`, `Lean.Meta.Tactic.Delta`, `Lean.Util.CollectAxioms`) in place of
`import Lean`, a file with the two imports of `Prim.lean` alone costs 10.95 G, 13.32 G with the
compiler of step 1 and 11.00 G with the compiler of step 2 (0.206, 0.250 and 0.207 GB). Against
`364e70a`, `Prim.lean`, `Encode.lean` and `PackedMul.lean` now cost 0.5 G more each and
`Walk.lean` 2.9 G more. A level file imports `Lean` through `Compute/Loader.lean` and gains
nothing from the change.

### What stays written by hand

- Unmarked definitions are not migrated. Those of the migrated files that are written with a raw
  recursor or `@Bool.rec`: `qorbit`, `qappl`, `qrowsOn` (`Quotient`); `sumSl`, `allFitQ`,
  `innerQ`, `cmpQ`, `checkPkQ`, `oP`, `oQ`, `checkOneQ` (`CheckQ`); `treeCheckQ` (`CuspQ`);
  `relWQ`, `starCheckQ` (`StarQ`); `absBig`, `rowsBig` (`FamQ`).
- Five notations went with their last user: `qt[…]`, `lt[…]` (`Quotient`), `dRowH[…]` (`DualQ`),
  `dgH[…]`, `eqvH[…]` (`CheckQ`). The others stay, each for an unmarked definition or a lemma
  statement: `cnt[…]`, `flds[…]`, `rd[…]`, `sgn[…]` (`Walk`; used by `selQ`, `sumSl`, `oP`, `oQ`,
  `checkOneQ`, `treeCheckQ`, `relWQ`, `rowsBig`, by the notations below, and by the statements
  of lemmas such as `weighPk_selQ`, `rd_eq_tblGet`, `decodeSp_eq`), `kc[…]`, `pt[…]`
  (`qorbit`, `qappl`, `qrowsOn`), `dRow[…]` (the statement of `dRow_eq`), `rel[…]`, `stRow[…]`
  (`relWQ`, `starCheckQ`, `relVal_eq`, `stRowQ_eq`), `dg[…]`, `fit[…]`, `eqv[…]` (`innerQ`,
  `allFitQ`, `cmpQ`), `andB[…]` (`famShape`, `famShapeVW`).
- The helpers the readable sources call, written out by the compiler (`@[kernel_inline]`): `rd`,
  `sgnBit` (`Walk`, beside `cnt` and `flds`), `qt`, `ltF`, `qlenRows` (`Quotient`), `dRow`, `dRowH`
  (`DualQ`), `dgH`, `eqvH` (`CheckQ`), `absI` (`FamQ`), `stepLevelsFrom` (`PackedColumnQ`).

## Step 3 in the tree

The definitions of the core that carried no mark and were still written by hand with a raw
recursor (`Nat.rec`, `List.rec`, `Bool.rec`), directly or through a notation, are `kernel_def`s,
under their names and with their arguments in their order: `qorbit`, `qappl`, `qrowsOn`
(`Compute/Pack/Quotient`), `selQ` (`Compute/Pack/BasisQ`), `sumSl`, `allFitQ`, `innerQ`, `cmpQ`,
`checkPkQ`, `oP`, `oQ`, `checkOneQ` (`Compute/Pack/CheckQ`), `treeCheckQ` (`Compute/Pack/CuspQ`),
`relWQ`, `starCheckQ` (`Compute/Pack/StarQ`), `absBig`, `rowsBig`, `famShape`, `famShapeVW`
(`Compute/Pack/FamQ`). Six of them are stated by the levels (`qappl`, `qrowsOn`, `treeCheckQ`,
`starCheckQ`, `famShape`, `famShapeVW`). None carries a mark (the mark is the owner's,
`docs/CFSG_EXPERIMENTS.md`, E14), and none is `noncomputable`. A search of every definition of
the core for a raw recursor finds no other, but two that stay written by hand: `stageQ` and
`lenStage` (`Cert/Hecke/HeilbronnQuot`), the recursions inside `qappl` and `qlen` restated for the
proofs. Their terms hold the arithmetic of the instances (`HMul.hMul …`), which the compiler
writes with the kernel's primitives (`Nat.mul …`), and no level states them, so they are left as
they are. `Levels/` was not regenerated: the core builds without a warning, `check_imports.py`
passes, and the level targets of step 2 (levels 23 and 997 of weight 2 with their `Newforms`,
level 37 of weights 4 and 6, level 39 of weight 2) build as they are.

### The term gate

`python3 scripts/bench/kernel_form/term_gate.py compare-unmarked
docs/bench/kernel_form/snapshot_unmarked`: exit 0. `snapshot_unmarked/` holds the terms of the 21
definitions before step 3, which are those of `364e70a` (no file of theirs had changed a term of
theirs). Their gate is that of a definition marked without `TODO`: identical, or identical up to
η, or up to the form of numerals where the hand term held `OfNat` numerals.

| file | definition | against the term before step 3 |
|---|---|---|
| `Compute/Pack/Quotient` | `qappl`, `qrowsOn` | identical |
| `Compute/Pack/Quotient` | `qorbit` | identical up to η |
| `Compute/Pack/BasisQ` | `selQ` | identical |
| `Compute/Pack/CheckQ` | `sumSl`, `allFitQ`, `innerQ`, `cmpQ`, `checkPkQ`, `oP`, `oQ`, `checkOneQ` | identical |
| `Compute/Pack/CuspQ` | `treeCheckQ` | identical |
| `Compute/Pack/StarQ` | `relWQ`, `starCheckQ` | identical |
| `Compute/Pack/FamQ` | `absBig`, `rowsBig`, `famShape`, `famShapeVW` | identical |
| `Cert/Hecke/HeilbronnQuot` | `stageQ`, `lenStage` | identical (written by hand, not migrated) |

The hand-written `qorbit` takes the row `rest` as a fifth argument of its recursor and carries it
unchanged through the motive; its readable source returns a function of `rest` in each case
(`| f + 1, X, u, v => fun rest ↦ …`), which gives that motive, with one binder fewer outside. No
numeral needed accepting. `term_gate.py compare docs/bench/kernel_form/snapshot_364e70a` on the
114 marked definitions: exit 0, the output of step 2 line for line.

The compiler showed one limit. It rejects a structural recursion on a `List (SRow ℤ)` ("the
recursive call … is not on a field of the constructor matched"): it finds the recursive fields of
a constructor by the head of their types after reducible unfolding, and `SRow ℤ`, the type of the
head of a cons, is an `abbrev` of a `List`. Nothing is added when it rejects. `innerQ` is written
with `List.foldr`, which gives the hand-written term; the compiler is unchanged.

### The proofs

No proof unfolds one of these kernel forms to its recursors any more. The `delta`s of the halving
comparisons of `CheckQ.lean` (`sumSlH_eq`, `allFitH_eq`, `wPH_eq`, `wQH_eq`, `cmpH_eq`, `oPH_eq`,
`oQH_eq`, `checkOneH_eq`) are inductions or rewritings with the readable equations, and so are
the `change`s that spelled out a recursor (`allFitQ_eq`, `innerQ_eq`, `cmpQ_eq` in `CheckQ`,
`treeCheckQ_eq` in `CuspQ`, `starCheckQ_eq` in `StarQ`, `rowsBig_iff` in `FamQ`, `qrowsOn_eq` in
`Cert/Hecke/HeilbronnQuot`). No statement changed. `rec_beq` (`HeilbronnQuot`: `Bool.rec` on
`Nat.beq` as an `if`) had no user left and went. Two lemmas are new: `eqv_row_eq` (`CheckQ`,
`cmp_row_eq` for the comparison as the readable definitions write it) and `stRow_def` (`StarQ`,
the helper `stRow` against the notation `stRow[…]` of the statements). The trailing `rfl`s of
`weighPkSlot_eq`, `checkPkQ_eq`, `cmp_row_eq`, of `hsc` in `checkOneQ_eq` and of `dRow_eq`
(`DualQ`) are still needed (each proof fails without it): their statements are written with
`Nat.*` heads and `cnt[…]`, the readable equations with the notation of `ℕ` and `decide`.

### The cost gate

`level_cost.py levels … after3 2:997` (`REPEATS=3 SKIP_REPEATS=2`), then `… after3 4:37 6:37 2:23`
(`REPEATS=5 SKIP_REPEATS=3`), against the rows `after2` (step 2).

| part | kernel G step 2 | step 3 | full G step 2 | step 3 | peak GB step 2 | step 3 |
|---|---:|---:|---:|---:|---:|---:|
| weight 2, 997, `Data` | 4.886 | 4.880 | 29.116 | 29.094 | 0.508 | 0.510 |
| weight 2, 997, `Basis` | 7.702 | 7.697 | 34.733 | 34.717 | 0.539 | 0.538 |
| weight 2, 997, `Hecke` | 32.210 | 32.058 | 70.484 | 70.456 | 0.856 | 0.856 |
| weight 2, 997, `QExp` | 4.578 | 4.592 | 37.269 | 37.280 | 0.668 | 0.668 |
| weight 2, 997, `Newforms` | 79.992 | 79.824 | 128.270 | 128.049 | 0.967 | 0.980 |
| weight 4, 37, `Data` | 0.192 | 0.201 | 24.332 | 24.316 | 0.447 | 0.447 |
| weight 4, 37, `Basis` | 6.850 | 6.817 | 32.404 | 31.771 | 0.490 | 0.498 |
| weight 4, 37, `Hecke` | 4.711 | 4.707 | 34.392 | 34.371 | 0.551 | 0.550 |
| weight 4, 37, `QExp` | 0.295 | 0.236 | 28.981 | 28.957 | 0.504 | 0.503 |
| weight 6, 37, `Data` | 0.193 | 0.200 | 24.340 | 24.319 | 0.447 | 0.447 |
| weight 6, 37, `Basis` | 21.672 | 21.671 | 46.904 | 46.870 | 0.675 | 0.676 |
| weight 6, 37, `Hecke` | 10.987 | 10.989 | 41.627 | 41.604 | 0.805 | 0.805 |
| weight 6, 37, `QExp` | 0.372 | 0.360 | 29.112 | 29.101 | 0.506 | 0.506 |
| weight 2, 23, `Data` | 0.133 | 0.133 | 24.258 | 24.238 | 0.446 | 0.446 |
| weight 2, 23, `Basis` | 0.172 | 0.182 | 25.349 | 25.343 | 0.452 | 0.452 |
| weight 2, 23, `Hecke` | 0.219 | 0.630 | 27.471 | 27.444 | 0.461 | 0.461 |
| weight 2, 23, `QExp` | 0.137 | 0.137 | 28.422 | 28.413 | 0.503 | 0.503 |
| weight 2, 23, `Newforms` | 0.681 | 0.673 | 31.621 | 31.598 | 0.523 | 0.524 |

The kernel figures are those of step 2 within the noise of the meter. `Hecke` at 23 reads 0.630
where step 2 read 0.219: the figure of step 2 was the odd one (0.603 at `364e70a`, 0.636 after
step 1), and the full runs read 27.471 and 27.444. The peak of `Newforms` at 997 reads 0.980
against 0.967, a minimum over runs that spread: 0.995, 0.997, 0.980 now, 0.971, 0.967, 0.997 in
step 2. The reviewer's side-by-side runs of `364e70a` and the tree after step 2
(`scripts/bench/kernel_form/head_ab.py`) put that file at 0.983 to 1.024 GB at `364e70a` and 0.972
to 1.012 in the tree, and `Hecke` at 997 at 0.837 to 0.841 and 0.839 to 0.843, with kernel G
32.56 and 32.18, 80.32 and 80.16: no rise of the peak.

`scripts/bench/kernel_form/starred_rows.sh TAG`: for each of the six definitions the levels state,
one check that reaches it, in copies, in the tree before the first edit of step 3 (tag `before3`)
and after it (`after3`); rows in `results_step3.jsonl`. Kernel G, full G (the steadier figure),
peak GB, and `hb`, the count of small allocations of the first copy, which does not vary from run
to run.

| check | reaches | hb before | after | kernel G before | after | full G before | after | peak GB before | after |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|
| weight 2, 997, `hPs13_163` × 1 | `qappl` | 14868 | 14868 | 12.085 | 12.676 | 38.660 | 40.083 | 0.833 | 0.833 |
| weight 2, 997, `hP3` × 4 | `qrowsOn` | 2242 | 2242 | 6.798 | 7.506 | 32.773 | 32.800 | 0.533 | 0.526 |
| weight 2, 997, `hTreeQ` × 20 | `treeCheckQ` | 191 | 191 | 3.419 | 3.411 | 29.593 | 29.582 | 0.465 | 0.466 |
| weight 2, 997, `hStarPQ` × 4 | `starCheckQ` | 2850 | 2850 | 7.612 | 7.647 | 33.490 | 33.499 | 0.537 | 0.537 |
| weight 2, 997, `hShPQ` × 20 | `famShapeVW` | 495 | 495 | 8.905 | 8.904 | 35.101 | 35.092 | 0.481 | 0.481 |
| weight 4, 37, `hShPQ` × 20 | `famShape` | 152 | 152 | 2.211 | 2.188 | 26.833 | 26.810 | 0.453 | 0.452 |

`hb` is the same to the unit for all six: the terms are the same. The kernel figures of
`hPs13_163` and `hP3` read 0.6 and 0.7 G higher; both were measured again with five full and
three short runs (tag `after3r`): `hPs13_163` 12.093 (12.085 before), and `hP3` 7.488 with a full
minimum of 32.695 (32.773 before), its runs without the kernel having fallen in a mode 0.75 G
lower than before (25.21 against 25.98).

### The cost of compiling the files

`REPEATS=3 python3 scripts/bench/kernel_form/level_cost.py files … TAG`, tags `before3` (the tree
before the first edit of step 3) and `after3`.

| file | full G before | after | wall s before | after | peak GB before | after |
|---|---:|---:|---:|---:|---:|---:|
| `Compute/Pack/Quotient.lean` | 18.755 | 18.553 | 2.45 | 2.54 | 0.314 | 0.311 |
| `Compute/Pack/BasisQ.lean` | 14.312 | 14.611 | 1.90 | 2.00 | 0.257 | 0.258 |
| `Compute/Pack/CheckQ.lean` | 25.755 | 25.147 | 2.94 | 3.00 | 0.336 | 0.332 |
| `Compute/Pack/CuspQ.lean` | 17.665 | 17.863 | 2.39 | 2.43 | 0.306 | 0.306 |
| `Compute/Pack/StarQ.lean` | 18.888 | 19.587 | 2.22 | 2.29 | 0.275 | 0.277 |
| `Compute/Pack/FamQ.lean` | 16.283 | 16.674 | 2.10 | 2.15 | 0.263 | 0.263 |
| `Cert/Hecke/HeilbronnQuot.lean` | 37.890 | 37.183 | 3.79 | 3.79 | 0.376 | 0.375 |

Within the spread of the meter (the three runs of `Quotient.lean` before read 19.746, 19.051,
18.755): the definitions compile at the cost of the hand-written ones, the equations they add
included.

The Lean files of `scripts/bench/kernel_form/` compile in the migrated tree (`build.py`), and
`build.py tests` behaves as described above, `Faults.lean` and `Rejects.lean` failing as they are
meant to.

### What stays written by hand

- `stageQ` and `lenStage` (`Cert/Hecke/HeilbronnQuot`), for the reason above. The recursions they
  restate are now also the helpers `qapplRows` and `qlenRows` of `Quotient.lean`, which the
  compiler writes out in `qappl` and `qlen`; `qappl_eq` and `qlen_eq` still state them through
  `stageQ` and `lenStage` (their proofs close by `rfl` on that recursion), since statements do
  not change.
- Six notations went with their last user: `kc[…]`, `pt[…]` (`Quotient`), `dg[…]`, `fit[…]`,
  `eqv[…]` (`CheckQ`), `andB[…]` (`FamQ`). Those that stay are used by lemma statements, which do
  not change: `cnt[…]`, `flds[…]` (`Walk`, scope `PackQ`; the statements of `cnt_eq`,
  `flds_eq`, `spCount_eq`, `decodeSp_eq`, `weighPk_selQ`, `packPk_selQ`, `weighPkSlot_eq`,
  `weighPkSlot_slotWQ`, `weighPkPN_bdWQ`, `weighPkN_relWQ`, `starTgt_tgtWQ`, and the notations
  `dRow[…]`, `stRow[…]`), `rd[…]` (`rd_eq`, `rd_eq_tblGet`, `wP_eq_selQ`, `wQ_eq_selQ`, the
  notation `rel[…]`), `sgn[…]` (`sgnBit_eq`, `fieldNeg_eq`, `selQ_succ`, and the proof of
  `selQ_add`), `dRow[…]` (`DualQ`: `dRow_def`, `dRow_eq`), `rel[…]` (`StarQ`: `relVal_eq`),
  `stRow[…]` (`StarQ`: `stRow_def`, `stRowQ_eq`), each with its `_eq` or `_def` lemma.
- The helpers the readable sources of this step call, written out by the compiler
  (`@[kernel_inline]`): `qcons`, `ptSlot`, `qapplRows` (a `kernel_def`) in `Quotient`; `dgQ`,
  `eqvQ` in `CheckQ`; `relImg`, `stRow` in `StarQ`.
- Four proofs of the earlier steps still state the recursor of a kernel form in a `change`, as
  they did when those steps were accepted: `rdH_succ` (`Walk`), `stepLevelsQ_aux` and
  `eqNatsQ_eq` (`PackedColumnQ`), `dsOk_eq` (`FamQ`). They compile and were not touched.

## The tag dropped

After step 3 the tag `[Kernel_Optimized]` was removed from the sources, at the owner's request:
`kernel_def` marks the definitions it marked. The 31 `TODO` tags became
`-- TODO: kernel form: …`, keeping only what the compiler does not change (pairs, an `Int`).
`term_gate.py compare DIR` now takes the definitions and their `todo` flag from `DIR/INDEX.json`,
which both snapshots of this folder carry, so the gate runs as before; `list` and `snapshot` scan
the `kernel_def`s of the core, and a snapshot taken with them has `todo` false everywhere, which
makes it the check that the compiler's output does not change (after a bump, for instance).

## Plain definitions against kernel forms, level 997

### The question

What does the compiler buy? The same sources at commit `25f6d27` in two variants, measured on the
five parts of level 997 of weight 2 (`Levels/Weight2/Level997/{Data, Basis, Hecke, QExp,
Newforms}.lean`, the level files and their data unchanged):

- K: the sources as they are, every one of the 136 `kernel_def`s evaluated in its kernel form;
- P: `kernel_def` is an ordinary `def` of its readable source, under the same name, modifiers and
  attributes kept, so that the kernel evaluates the readable definition: arithmetic through the
  instances, `if` through a `Decidable` instance, `&&`, `match` through its matcher, structural
  recursion through `brecOn`. Everything else is the same: the plain `def`s, the
  `@[kernel_inline]` helpers (in P ordinary functions, called from the readable sources), the
  level files, the data.

### The answer

The kernel forms halve the kernel's work on the level: 104.9 G of kernel instructions over the
five parts in K against 206.1 G in P (P/K = 1.97), 7.5 s of kernel time against 17.7 s, and 26.5 s
against 36.8 s of wall time for the five files in full. The peak of `Hecke` goes from 0.73 to
1.91 GB, which makes it the peak of the level. Elaboration does not change: the runs without the
kernel cost the same in both variants, to 0.03 G, with the same peak. The difference is in the
one-vector checks of `Hecke` and the products row by row of `QExp` and `Newforms`, and, by
definition, in the column of a point (`qappl` and the recursions under it: 25 % of the difference),
the halving reads (`rdH`, `rdL`: 22 %), the product row by row (`dotH`, `slotSumH`, `rowEq`,
`rowsEq`: 16 %) and the walks of the one-vector check (`oPH`, `oQH`, `sumSlH`, `checkOneH`,
`lenN`: 11 %), in allocations (below).

| part | kernel G K | P | P/K | full G K | P | peak GB K | P | wall s K | P |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `Data` | 4.257 | 8.265 | 1.94 | 21.052 | 25.055 | 0.403 | 0.501 | 3.44 | 3.85 |
| `Basis` | 6.173 | 22.563 | 3.66 | 25.146 | 41.561 | 0.433 | 0.584 | 3.73 | 5.15 |
| `Hecke` | 26.270 | 81.546 | 3.10 | 53.512 | 108.786 | 0.733 | 1.913 | 5.80 | 12.25 |
| `QExp` | 3.533 | 8.279 | 2.34 | 27.098 | 31.834 | 0.553 | 0.760 | 4.15 | 4.57 |
| `Newforms` | 64.638 | 85.467 | 1.32 | 100.348 | 121.163 | 0.871 | 0.873 | 9.33 | 10.96 |
| all five | 104.871 | 206.120 | 1.97 | 227.156 | 328.399 | 0.871 | 1.913 | 26.45 | 36.78 |

The full runs of a file agree to 0.1 G and their peaks to 0.04 GB, but for two files: the full runs
of `Data` in K read 22.48, 22.31 and 21.05 (with the middle one its kernel figure would be 5.5 G and
P/K 1.5), and one run of three of `Newforms` reads 0.3 G (K) and 1.1 G (P) above the two others.
One of the two runs without the kernel of `Basis` and of `QExp` falls 0.2 to 1.2 G above the other,
in both variants. No run came near the caps (24 GB, 1800 s). `Newforms` gains least: its heaviest
checks (`hMinor<i>`, `hLin3`, `hNewTable`) cost the same in both variants, to 5 % in allocations.

### Method

`scripts/bench/kernel_form/plain_ab.py`, on the model of `head_ab.py`.

- Both variants are taken from `git archive 25f6d27` (the core and `Levels/Weight2/Level997`),
  never from the working tree, into `KERNEL_FORM_WORK/plain_ab/{K,P}/src`. P is K with
  `scripts/bench/kernel_form/plain_ab_P.patch` applied: the command `kernel_def` of
  `Compute/KernelForm.lean` elaborates `def` of what is written, and twelve proofs of eight files
  of the core are adapted, with eight lemmas added (below).
- The 60 modules of the core downstream of `Compute/KernelForm.lean` are compiled into a library of
  each variant (`{K,P}/lib`), K too; the 76 others are copied from the repository's build, after a
  check that their sources are those of the commit. The search path of a variant has no entry for
  the repository's own build. All 60 modules compile in P without a warning, the two acceptance
  files (`Cert/Acceptance/Level11`, `Forms/QExpBasis/Acceptance/Level11`, checked by
  `decide +kernel`) included.
- The four first parts are compiled on each library, then each part is run 3 times in full and 2
  times with `-Ddebug.skipKernelTC=true` in each variant, the two variants in turn, with the options
  of `level_cost.py` (`-j1`, `-DElab.async=false`); kernel G is the difference of the two minima.
  The figures are not those of the tables above this section, taken under Lean `v4.36`: at
  `v4.37.0-rc1` the same files cost 7 to 13 G less without the kernel, and the kernel figures of K
  are lower too. Only the columns of one table compare.
- One option is added to every run of a level file, in both variants: `-DmaxRecDepth=8192`. In P
  the bridges of `Basis` (`hDualP`, `hDualM`: `dualStackH_eq … rfl …`) pass the default depth of
  512 in the elaborator, which checks the `rfl` arguments (constants such as the ones row of the
  dual check) by unfolding the readable definitions. The option is a limit: it changes nothing in
  a run that does not reach it, and K does not.
- Apple M5, 32 GB, shared with a second agent, one heavy job at a time.

### Where the difference is

`plain_ab.py heartbeats` runs each part once in each variant with `#count_heartbeats in` before
every `decide +kernel` theorem: `hb`, the small allocations of each check in thousands, which do
not vary from run to run and follow the kernel's instructions (P/K 3.23 in `hb` and 3.10 in kernel
G for `Hecke`). By part, the checks that carry the difference (`hb` K, then P):

- `Data` (5373, 11718): the walk of the cusps `hWalk` 2345 to 5857, the four table checks `hS`,
  `hT`, `hTT`, `hStar` (`rowTblOk`, through `rowPtOk`, `crossEqNat`, `ptC`, `ptD`) 466 to 1140 each.
- `Basis` (10337, 34907): the star checks `hStarPQ`, `hStarMQ` 6241 to 17067, the dual checks
  `hDualPQ`, `hDualMQ` 2360 to 10454, the shape checks `hShPQ`, `hShMQ` 1000 to 4442, the cusp
  checks 390 to 1930.
- `Hecke` (39295, 127005): the one-vector checks, `hPs13_163` 15030 to 62768 (54 % of the
  difference), `hP2` to `hP11` 15450 to 53949; the recursion checks `hStepQ<p>` gain 116 to 270
  each.
- `QExp` (5401, 12314): `hO1R` 4142 to 11020, the product row by row (`e2RowsCheck`).
- `Newforms` (88564, 119975): the eight `hEig<i>` 16705 to 43900 (87 % of the difference), the
  same product row by row; the eight `hTab<i>` 4456 to 6516 (7 %); the rest by 0 to 5 %.

The two parts with the largest difference, theorem by theorem (`plain_ab.py theorems`: the check
alone in a file with the preamble of its part, 3 runs in full and 2 without the kernel in each
variant; `copies` copies made distinct, README "the meter's noise"). Kernel G, peak GB:

| part | check | copies | kernel G K | P | `hb` K | P | peak GB K | P |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| `Hecke` | `hPs13_163` | 1 | 10.637 | 39.994 | 15030 | 62768 | 0.727 | 1.909 |
| `Hecke` | `hP11` | 1 | 1.908 | 10.508 | 4211 | 16437 | 0.462 | 0.764 |
| `Hecke` | `hP7` | 1 | 2.229 | 7.912 | 3327 | 12327 | 0.436 | 0.662 |
| `Hecke` | `hP5` | 1 | 1.939 | 7.302 | 2844 | 10150 | 0.422 | 0.611 |
| `Hecke` | `hP3` | 1 | 1.544 | 4.434 | 2284 | 7761 | 0.405 | 0.552 |
| `Hecke` | `hP2` | 1 | 1.901 | 4.679 | 2784 | 7274 | 0.420 | 0.537 |
| `Hecke` | `hStepQ2` | 1 | 2.020 | 2.155 | 3268 | 3538 | 0.457 | 0.466 |
| `Newforms` | `hEig3` | 3 | 3.800 | 10.699 | 2092 | 5490 | 0.459 | 0.577 |
| `Newforms` | `hEig7` | 3 | 4.029 | 9.709 | 2096 | 5502 | 0.490 | 0.606 |
| `Newforms` | `hTab7` | 3 | 10.633 | 10.124 | 560 | 824 | 0.779 | 0.785 |
| `Newforms` | `hLin3` | 1 | 9.608 | 8.484 | 15425 | 15448 | 0.862 | 0.862 |
| `Newforms` | `hMinor7` | 1 | 3.397 | 2.342 | 3356 | 3519 | 0.508 | 0.512 |
| `Newforms` | `hNewTable` | 1 | 6.535 | 6.499 | 10527 | 10546 | 0.772 | 0.773 |

(`hb` of one copy.)

A check of 2 to 3 G read alone moves by up to 1 G from batch to batch (`hP11` in K: 1.91 G here,
2.95 G in the batch of the mixed variants below; `hMinor7` and `hLin3` read 1 G lower in P than
in K, where `hb` says they are the same to 5 %). `hb` does not follow the instructions of a check
whose work is arithmetic on big numbers (`hTab7`: 560 `hb` for 3.5 G a copy, the same in both
variants), but it does for the walks. The one-vector checks lose more in P the larger the prime:
`hb` P/K is 2.6 for `hP2` (no column built from the quotient form), then 3.4, 3.6, 3.7, 3.9 for
`hP3` to `hP11` and 4.2 for `hPs13_163` (the primes 13 to 163), with the length of the columns
built by `qappl`.

### Which definitions

Four mixed variants say which definitions carry the difference: the sources of K with its
compiler, but for one group of definitions, which stay ordinary definitions (and the proofs of P
for the files those definitions break: `Walk.lean` for `Mread`, `HeilbronnQuot.lean` for
`Morbit`). All four compile without another change.

- `Mread`: the halving reads `rdH`, `rdL`;
- `Mwalk`: the walks of the one-vector check `oPH`, `oQH`, `sumSlH`, `checkOneH`, and `lenN`;
- `Morbit`: the column of a point, `qappl`, `qapplRows`, `qorbit`, `qrow`, `qdigits`, `qlen`,
  `qlenRows`, `qsteps`, `tabKey`, `tabSlot`, `ptC`, `ptD`;
- `Mdense`: the product row by row, `dotH`, `slotSumH`, `rowEq`, `rowsEq`.

Kernel G, then peak GB (`measure` and `theorems` with `PLAIN_AB_TAG=mixed`, in one batch, so K
and P were measured again beside them; an empty cell: not run, the group is not reached):

| | K | P | `Mread` | `Mwalk` | `Morbit` | `Mdense` |
|---|---:|---:|---:|---:|---:|---:|
| `Hecke`, kernel G | 26.385 | 81.696 | 36.832 | 35.713 | 52.871 | |
| `Hecke`, peak GB | 0.730 | 1.911 | 0.798 | 0.994 | 1.591 | |
| `hPs13_163`, kernel G | 9.968 | 40.027 | 14.324 | 15.419 | 30.175 | |
| `hPs13_163`, peak GB | 0.729 | 1.909 | 0.791 | 0.988 | 1.585 | |
| `hP11`, kernel G | 2.946 | 10.521 | 4.769 | 4.380 | 5.707 | |
| `Newforms`, kernel G | 65.292 | 86.062 | 69.862 | | | 77.398 |
| `hEig7` × 3, kernel G | 4.031 | 10.932 | 5.682 | | | 9.065 |

`hb` of the whole level by group (`heartbeats` in all six variants; P − K is 156949):

| part | P − K | `Mread` − K | `Mwalk` − K | `Morbit` − K | `Mdense` − K |
|---|---:|---:|---:|---:|---:|
| `Data` | 6345 | 0 | 211 | 520 | 0 |
| `Basis` | 24570 | 5709 | 99 | 0 | 0 |
| `Hecke` | 87710 | 20421 | 15115 | 37958 | 0 |
| `QExp` | 6913 | 1673 | 97 | 0 | 4960 |
| `Newforms` | 31411 | 6581 | 1856 | 0 | 19494 |
| level | 156949 | 34384 | 17378 | 38478 | 24454 |

The groups add up: in `hPs13_163` the three increments are 4.4, 5.5 and 20.2 G, 30.0 G together
against 30.1 G for P; in `hEig7` 1.7 and 5.0 G against 6.9 G; in `hb`, 99 % of the difference of
`hPs13_163` and 96 % of that of the `hEig<i>`. So, by definition:

- The column of a point (`Morbit`) is the largest share: 26.5 of the 55.3 G that `Hecke` loses,
  20.2 of the 30.1 G of `hPs13_163`, and the peak: with this group alone readable, `Hecke` peaks at
  1.59 GB of the 1.91 GB of P. Its definitions are the recursions with the most arguments that
  change from step to step (`qdigits` four of five, `qorbit` three and the row in front of which it
  writes). Why the readable recursion takes the memory (its `brecOn`, the matchers, the `Decidable`
  instances of the tests) was not looked into.
- The halving reads (`Mread`): 10.4 G in `Hecke`, 4.6 G in `Newforms`, and most of the dual
  checks of `Basis` (`hb` 2360 in K, 8069 with the reads readable, 10454 in P).
- The walks of the one-vector check (`Mwalk`): 9.3 G in `Hecke`.
- The product row by row (`Mdense`): 12.1 G of the 20.8 G of `Newforms`, and 4960 of the 6913
  `hb` of `QExp`; with the reads, 96 % of the `hb` of the `hEig<i>` and of `QExp`.
- Not split: a quarter of the difference in `hb`. The star, shape, cusp and tree checks of `Basis`
  and the rest of its dual checks (`starCheckQ`, `relWQ`, `tgtWQ`, `famShapeVW`, `rowsBig`,
  `absBig`, `dsOk`, `cuspCheckSQ`, `bdWQ`, `treeCheckQ`, `dualStackH`, `rowsDualH`, `slotWH`,
  `relKillsH`: 18762 `hb`), the table and walk checks of `Data` (5614), and in `Hecke`, mostly in
  `hP2` to `hP11`, the halving form of the tally check (`checkPkH`, `allFitH`, `innerH`, `cmpH`,
  `wPH`, `wQH`, `qrowsOn`: 14216).

### The proofs adapted in P

`plain_ab_P.patch`. Nothing in the core uses `Src.f` or `f.eq_src`. What breaks is of two kinds:
a proof that states a recursor of a kernel form (`change`, the four of the brief), and a proof
by `rfl` of an equation between two kernel forms, or between a kernel form and a statement written
with recursors, which holds by unfolding in K and needs an induction or a case split in P. No
statement of the core changes but one auxiliary lemma (`stepLevelsQ_aux`); no `sorry`.

- `Compute/KernelForm.lean`: the elaborator of `kernel_def` is `def` of what is written.
- `Compute/Pack/Walk.lean`, `rdH_succ`: `rw [rdH, Nat.one_shiftLeft, Nat.one_shiftLeft,
  Nat.and_two_pow_sub_one_eq_mod]` in place of a `change` to the recursor.
- `Compute/Pack/BasisQ.lean`, `selQ_succ` (was `rfl`): `rw [selQ]`, a split of the `if`, and the
  test `Nat.beq (sgn[…]) e` rewritten to its value.
- `Compute/Pack/CuspQ.lean`: new `bdWQ_eq_selQ` (induction); `weighPkPN_bdWQ` rewrites with it
  in place of a closing `rfl`.
- `Compute/Pack/DualQ.lean`: new `slotWQ_eq_selQ` (induction); `weighPkSlot_slotWQ` likewise.
- `Compute/Pack/StarQ.lean`: new `relWQ_eq_selQ`, `tgtWQ_one_eq_selQ`, `tgtWQ_zero_eq_selQ`
  (inductions) and `relImg_eq` (the helper `relImg` against the notation `rel[…]`, by a split);
  `weighPkN_relWQ` and `starTgt_tgtWQ` rewrite with them.
- `Compute/Pack/FamQ.lean`: `dsOk_eq` (a `change` to `Nat.*` heads and a case split, in place of
  a `change` to the recursor); `absBig_succ` (was `rfl`): a split, as `selQ_succ`.
- `Compute/PackedColumnQ.lean`: `stepLevelsQ_aux` is stated on `stepLevelsFrom` in place of the
  raw `Nat.rec` it unfolded to, and proved by its equations and a case split; `eqNatsQ_eq` by
  `congrArg` in place of a `change` to the recursor.
- `Cert/Hecke/HeilbronnQuot.lean`: new `qapplRows_eq_stageQ`, `qlenRows_eq_lenStage`
  (inductions); `qappl_eq` and `qlen_eq` (was `rfl`) rewrite with them.

### What was not done

- One level, one weight, one toolchain (`v4.37.0-rc1`); levels 23 and 37 and weights 4 and 6 were
  not measured.
- Which construct of a readable definition costs (the instances of the arithmetic, the `Decidable`
  instances of the tests, the matchers, `brecOn`) was not separated, nor why the column of a point
  takes the memory.
- The mixed variants split the one-vector check and the product row by row only; the star, shape,
  cusp and dual checks of `Basis` and the checks of `Data` were not split by definition.
- No compile time of the core in P against K (the 60 modules were compiled six at a time), and no
  audit of the axioms of the variants (`lake exe axioms` is not run on scratch libraries).

### To run it again

From the repository root, each line under the machine's lock, with `KERNEL_FORM_WORK` set and
`A=scripts/bench/kernel_form/plain_ab.py`:

```
python3 $A prepare K P Mread Mwalk Morbit Mdense
python3 $A build K P Mread Mwalk Morbit Mdense
python3 $A levels K P Mread Mwalk Morbit Mdense
python3 $A measure OUT.jsonl 3 2
python3 $A heartbeats OUT.jsonl
python3 $A theorems OUT.jsonl Hecke 'only=hPs13_163|hP2|hP3|hP5|hP7|hP11|hStepQ2'
python3 $A theorems OUT.jsonl Newforms 'only=hEig7|hEig3|hTab7' copies=3
python3 $A theorems OUT.jsonl Newforms 'only=hLin3|hMinor7|hNewTable'
export PLAIN_AB_TAG=mixed
PLAIN_AB_VARIANTS=K,P,Mread,Mwalk,Morbit python3 $A theorems OUT.jsonl Hecke 'only=hPs13_163|hP11'
PLAIN_AB_VARIANTS=K,P,Mread,Mdense python3 $A theorems OUT.jsonl Newforms 'only=hEig7' copies=3
PLAIN_AB_VARIANTS=K,P,Mread,Mwalk,Morbit python3 $A measure OUT.jsonl 3 2 Hecke
PLAIN_AB_VARIANTS=K,P,Mread,Mdense python3 $A measure OUT.jsonl 3 2 Newforms
PLAIN_AB_VARIANTS=K,P,Mread,Mwalk,Morbit,Mdense python3 $A heartbeats OUT.jsonl
python3 $A report OUT.jsonl
```

The rows of this section are in `plain_vs_kernel.jsonl` (`exp`: `part`, `hb`, `thm`; the rows of
the mixed variants carry `tag: mixed`).

## `swarOk`

After the measurement above (which is at commit `25f6d27`), `swarOk`, the SWAR range check of
`Compute/Pack/Walk.lean`, became a `kernel_def`, at the owner's request: a plain definition written
with `Nat.*` heads that the kernel evaluates in every level (`rowsOk`, `e2RowsCheck`,
`colTableOk`). Its source is the statement of `swarOk_iff` as a `Bool`. Against its hand-written
term (`snapshot_swarOk/`) the kernel form has `Bool.rec` where `&&` was and raw literals, the same
operations otherwise. `tests/SwarAB.lean` states the bounds of the five Hecke tables of level 997
(`rowsOk 27 82 82 0 24 (MT p)`, 82 rows each) on the hand-written form and on the `kernel_def`, on
the same toolchain: 362 and 353 thousand heartbeats.

## Step 4: the plain definitions the kernel evaluates

A walk of the compiled environment from the theorems the levels prove by `decide +kernel` found
the ordinary `def`s the kernel still unfolded. Two groups of them, 86 definitions, were to become
`kernel_def`s under their names, with their arguments in their order (the levels name them, and
`Levels/` was not regenerated):

- the shared walkers and the weight-2 engine (45): `allIdx`, `allLt`, `allZip`, `biasRow`, `ones`,
  `rowsOk`, `tblLt` (`Compute/Pack/Walk`); `e2InOk`, `e2OutOk`, `e2RowsCheck`, `e2StackCheck`,
  `stackEq`, `strideOk` (`Compute/PackedDense`); `colMask`, `mulCols`, `sumCols`
  (`Compute/PackedStack`); `colStepOk`, `colTableOk`, `colUnitOk`, `colZeroOk`, `eqNats`,
  `stepCoeff`, `stepLevels`, `stepPrev` (`Compute/PackedColumn`); `colStepOkQ`
  (`Compute/PackedColumnQ`); `echelonOk`, `pivotRow`, `pivotsOk` (`Compute/PackedQExp`);
  `pointKeyOk`, `pointsKeyOk`, `rowTblOk` (`Compute/Pack/Points`); `facOk`, `keyAt`, `p1Key`
  (`Compute/P1Key`); `tabOk` (`Compute/P1KeyTab`); `isPrimeB`, `minFac'`, `minFacFrom`
  (`Compute/Primes`, which now imports `Compute/KernelForm`); `cuspPN`, `cuspWalk`, `cuspWalkOk`,
  `det1PN`, `genCuspOk`, `recPN` (`Compute/Pack/Cusps`); `bdSelS` (`Compute/Pack/PlusImg`);
- the newform certificate, `Forms/Newform/Compute/` (41): `compSlotOk`, `compSlots`,
  `companionOk`, `evalModOk`, `hornerMod`, `normOk` (`Checks`); `coeffsModOk`, `resMod`, `slotRes`
  (`Irreducible`); `detOk`, `orbitSlotsOk`, `slotsEqOk`, `tableRowsOk` (`Level`); `minorOk`,
  `modEntryOk`, `modOneOk`, `modRowsOk`, `modSlotsOk`, `zeroRowOk` (`Minor`); `accL`, `combOk`,
  `evalCoordsMod`, `genOk`, `linAcc`, `linRowsOk`, `minorAtOk`, `mulAccOk`, `mulCoordsOk`,
  `mulRowOk`, `rootStep`, `rowsLinOk`, `slotsSignedOk`, `stepL`, `unpackL` (`Operator`);
  `frobProdOk`, `monicPk`, `polyMulModOk`, `powSteps`, `rowModOk`, `rowSteps`, `rowVal`
  (`PolyMul`).

84 are `kernel_def`s. Their bodies are written in the notation of `ℕ` (`a + b`, `a ≤ b`,
`x &&& mask K`, `u >>> K`, `if`, `&&`, `==`, `List.all`, `List.map`, pattern matching, numerals).
Calls of named definitions stay calls: `pow2 K` is not written `2 ^ K`, so that the kernel term
keeps its `Nat.shiftLeft`. The sources of `stepPrev` and `stepCoeff` are now the statements of their
`_eq` lemmas (`if p ∣ n / p then …`, `if p.Coprime N then …`): the compiler writes both tests as
the `Nat.beq` of the hand-written forms, and the kernel terms are those of `25f6d27` up to the
unfolding of `cond` (checked below). Where a body used `List.all` or `List.map` (`rowsOk`, `facOk`,
`tabOk`, `e2InOk`, `e2OutOk`, `e2StackCheck`, `strideOk`, `echelonOk`, `colTableOk`, `colStepOk`,
`colStepOkQ`, `genOk`, `frobProdOk`, `coeffsModOk`), the kernel form has a bare `List.rec` in its
place.

Two are left as they were, written by hand: `powSteps` and `rowSteps` (`PolyMul`). The compiler
rejects both ("the recursive call … is not on a field of the constructor matched"): `powSteps`
recurses on the list after three cells (`y :: q :: t :: W`), `rowSteps` on `y :: rows`, a cell
rebuilt from the pattern `x :: y :: rows`. Lean's structural recursion accepts both through
`brecOn`; the compiler only follows a recursive call on the field of the constructor it matched. A
form it accepts would walk the list one cell at a time and carry the cells already read, which
changes the definition and its two specifications more than a rewriting, so neither was changed.
Nothing is added when the compiler rejects a definition, so the first attempt left the two names
undefined and was reverted to the text of `25f6d27`.

### The correctness test

`scripts/bench/kernel_form/tests/Step4Eq.lean` holds the 84 replaced definitions verbatim from
`git show 25f6d27:<file>`, in a namespace `Old` of their own namespace, callers first, so that
every name in a body but the definition itself resolves to the definition of the tree; for each,
`Step4Eq.f_eq : @Old.f = @f` or its pointwise form. It compiles without an error, a warning or a
`sorry` (`lake env lean -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false …`, under the lock).

- `rfl` (37): `isPrimeB`, `minFac'`, `biasRow`, `ones`, `tblLt`, `colMask`, `e2RowsCheck`,
  `stackEq`, `pivotRow`, `stepLevels`, `pointKeyOk`, `pointsKeyOk`, `rowTblOk`, `recPN`, `cuspPN`,
  `det1PN`, `genCuspOk`, `cuspWalkOk`, `companionOk`, `compSlotOk`, `normOk`, `evalModOk`,
  `zeroRowOk`, `modOneOk`, `minorOk`, `tableRowsOk`, `detOk`, `minorAtOk`, `mulCoordsOk`,
  `mulRowOk`, `rootStep`, `rowsLinOk`, `monicPk`, `polyMulModOk`, `rowVal`, `rowModOk`, `resMod`.
- `kernel_rfl%` (6): `keyAt`, `colZeroOk`, `stepPrev`, `stepCoeff`, `bdSelS`, `modEntryOk`. The
  kernel finds the two terms equal; the elaborator's unifier does not see through the `bif` (`cond`),
  the `let` or the `match` of the plain definition against the `Bool.rec` of the kernel form.
  `kernel_rfl%` (defined in the test file, as in `tests/SpecEq.lean`) is `Eq.refl` at the stated
  type, which only the kernel compares.
- `rw [f]` and then `rfl` against the readable body (14): `tabOk`, `facOk`, `rowsOk`,
  `e2InOk`, `e2OutOk`, `e2StackCheck`, `strideOk`, `echelonOk`, `colTableOk`, `colStepOk`,
  `colStepOkQ`, `genOk`, `frobProdOk`, `coeffsModOk`: the plain definition calls `List.all` or
  `List.map`, the kernel form a `List.rec`, and the two are equal on a variable list only by
  induction, which the readable equation does once and for all.
- a case split on the list (1): `colUnitOk` (overlapping patterns).
- an induction with the readable equations (26): every recursive definition, `minFacFrom`,
  `p1Key`, `allLt`, `allZip`, `allIdx`, `mulCols`, `sumCols`, `pivotsOk`, `eqNats`, `cuspWalk`,
  `compSlots`, `hornerMod`, `modRowsOk`, `modSlotsOk`, `orbitSlotsOk`, `slotsEqOk`,
  `evalCoordsMod`, `mulAccOk`, `slotsSignedOk`, `accL`, `stepL`, `linRowsOk`, `unpackL`, `combOk`,
  `linAcc`, `slotRes` (a structural recursion through `brecOn` against a bare recursor).

So `rfl` was not enough for 47 of the 84, `kernel_rfl%` included.

### The proofs

No statement changed and no lemma was added. Most of the proofs that broke named the old heads in a
`simp only` (`Nat.blt_eq`, `Nat.ble_eq`, `Nat.beq_eq`, `Nat.add_eq`, …): the readable equations
give `decide (a < b)` and `a == b`, read by `decide_eq_true_eq` and `beq_iff_eq`, and the unused
arguments went. The others:

- a proof that unfolded a recursive definition by `change` saw its recursor after one step and lost
  the recursive call: `cast_hornerMod` (`Checks`) and `cast_evalCoordsMod` (`Operator`) rewrite with
  `rw [f]`;
- a proof that applied a lemma about `List.all`, `allLt` or `slotsSignedOk` to the check itself,
  by unification through the plain definition, rewrites the hypothesis first: `tabOk_spec`
  (`P1KeyTab`), `facOk_spec` (`P1Key`), `rowTblOk_spec` (`Points`), `mulAccOk_spec` (`Operator`);
- `x &&& mask K` where the old body had `Nat.land x (mask K)`: `compSlots_spec`, `linAcc_spec`,
  `slotsSignedOk_spec`, `slotsEqOk_spec` add `Nat.land_eq`; `compSlotsH_eq` drops two
  `Nat.shiftRight_eq`;
- `getD_map_shiftRight` and `getD_map_mul` (`Operator`) are stated on `Nat.shiftRight u K` and
  `Nat.mul a`, the readable sources write `u >>> KM` and `den * ·`: `combOk_spec` and `genOk_spec`
  state the instance they need in a `have` proved by the lemma;
- `minorOk_spec` (`Minor`) states its shift `(s + Ce + ε * (ℓ - 1)) % ℓ` in notation and
  generalizes it before `push_cast`, which would otherwise push the cast through the `%`;
  `modEntryOk_spec` drops the auxiliary `hδ` on `cond`, now an `if` that `push_cast` reads;
- `stepPrev_eq`, `stepCoeff_eq` (`PackedColumn`) are `rw [f]`, their statements being the sources;
  `eqNatsQ_eq` (`PackedColumnQ`) rewrites with the two readable equations in place of a `change` to
  the recursor and a case split; `keyAt_eq` (`P1Key`), `getD_stepL`, `getD_accL` (`Operator`) lost a
  trailing `rfl`.

By file: `Compute/Primes` (`isPrimeB_iff`), `Compute/P1Key` (`keyAt_eq`, `facOk_spec`,
`p1Key_unit_mul`), `Compute/P1KeyTab` (`tabOk_spec`), `Compute/Pack/Walk` (`allIdx_getD`,
`natAbs_denseMatPk_le_of_rowsOk`, `sub_biasRow_eq_sum`, `biasRow_succ`), `Compute/PackedStack`
(`mulCols_packNat`, `sumCols_packNat`), `Compute/PackedDense` (`rowIds_of_stackEq`, `e2InOk_spec`,
`e2OutOk_spec`, `mul_eq_of_e2StackCheck`, `mul_eq_of_e2RowsCheck`, `stackEq_of_rowIds`,
`e2StackCheck_of_e2RowsCheck`), `Compute/PackedQExp` (`pivotsOk_spec`, `slot_pivot_of_echelonOk`,
`pivot_mem_of_echelonOk`), `Compute/PackedColumn` (`colTableOk_spec`, `colZero_spec`,
`colUnitOk_spec`, `mem_stepLevels`, `stepPrev_eq`, `stepCoeff_eq`, `eq_of_eqNats`,
`colStepOk_spec`), `Compute/PackedColumnQ` (`eqNatsQ_eq`), `Compute/Pack/Points`
(`pointsKeyOk_spec`, `rowTblOk_spec`), `Compute/Pack/Cusps` (`cuspWalk_spec`, `cuspWalkOk_spec`),
`Cert/Model/Cusps` (`entry_spec`), `Forms/Newform/Compute/Checks` (`compSlotOk_spec`,
`compSlots_spec`, `companionOk_spec`, `compSlotsH_eq`, `pos_of_normOk`, `normOk_spec`,
`cast_hornerMod`, `evalModOk_spec`), `Minor` (`zeroRowOk_spec`, `modEntryOk_spec`,
`modOneOk_spec`, `minorOk_spec`), `Level` (`slotsEqOk_spec`, `sum_eq_of_tableRowsOk`,
`rowOk_of_tableRowsOk`, `det_ne_zero_of_detOk`), `Operator` (`linAcc_spec`, `combOk_spec`,
`rowsLinOk_spec`, `getD_stepL`, `getD_accL`, `slotsSignedOk_spec`, `mulAccOk_spec`,
`mulCoordsOk_spec`, `genOk_mem`, `genOk_spec`, `cast_evalCoordsMod`, `one_lt_of_minorOk`,
`minorAtOk_spec`), `PolyMul` (`kronPoly_eq_of_polyMulModOk`, `slot_sub_eq_of_rowModOk`,
`modElem_rowVal_pow`, `rowModOk_of_frobProdOk`), `Irreducible` (`resRow_eq_of_coeffsModOk`). The
proofs that rest on the definitional unfolding of a check into its conjuncts
(`e2RowsCheck_of_blocks`, `companionOk_of_blocks`, `mulCoordsOk_of_blocks`) are unchanged: the
elaborator unfolds the kernel forms there.

Docstrings: the module docstrings of `PackedStack`, `PackedDense`, `PackedQExp`, `PackedColumn` and
the docstring of `mulCols` said that the checks are written with explicit `Nat.*` heads; they now
say that they are `kernel_def`s evaluated with them.

### The builds

The core builds without a warning (`lake build`, 9445 jobs), `check_imports.py` passes, and the
level targets build as they are: levels 23 and 997 of weight 2 (five parts each), level 39 of
weight 2 and level 37 of weights 4 and 6 (four parts each), 9461 jobs, no warning. The term gates
of the earlier definitions print, line for line, what they printed before the first edit of this
step (`term_gate.py compare docs/bench/kernel_form/snapshot_364e70a` and `compare-unmarked
docs/bench/kernel_form/snapshot_unmarked`, both exit 0).

### The cost gate

`REPEATS=3 SKIP_REPEATS=2 level_cost.py levels docs/bench/kernel_form/level_cost.jsonl TAG 2:997`,
tags `before4` (the tree before the first edit, with `swarOk` already a `kernel_def`) and `after4`,
on `v4.37.0-rc1`.

| part | kernel G before | after | full G before | after | peak GB before | after |
|---|---:|---:|---:|---:|---:|---:|
| weight 2, 997, `Data` | 4.713 | 3.335 | 21.517 | 20.135 | 0.402 | 0.403 |
| weight 2, 997, `Basis` | 6.151 | 6.152 | 25.139 | 25.130 | 0.425 | 0.428 |
| weight 2, 997, `Hecke` | 26.259 | 25.219 | 53.511 | 52.478 | 0.733 | 0.734 |
| weight 2, 997, `QExp` | 3.089 | 3.399 | 26.679 | 26.977 | 0.550 | 0.548 |
| weight 2, 997, `Newforms` | 64.676 | 45.799 | 100.413 | 82.446 | 0.872 | 0.776 |
| all five | 104.888 | 83.904 | 227.259 | 207.166 | 0.872 | 0.776 |

`Newforms` loses 29 % of its kernel work and its peak falls by 0.1 GB, `Data` 29 %, `Hecke` 4 %;
`Basis` does not move (its `hb` is the same to the unit). `QExp` reads 0.3 G higher, within
the noise of the meter: its three full runs before were 27.377, 28.722, 26.679 (the minimum an
outlier below the two others), after 26.977, 26.993, 26.992, and its `hb` fell by 249.

`scripts/bench/kernel_form/step4_heartbeats.py run docs/bench/kernel_form/step4_heartbeats.jsonl TAG
2:997` (new, beside `plain_ab.py`): each part of the level, in place, with `#count_heartbeats in`
before every `decide +kernel` theorem, once (`hb`, thousands of small allocations, which do not
vary from run to run). 128 checks: none rises, 96 fall, 32 do not move.

| part | `hb` before | after |
|---|---:|---:|
| `Data` | 5373 | 4014 |
| `Basis` | 10337 | 10337 |
| `Hecke` | 39271 | 37735 |
| `QExp` | 5396 | 5147 |
| `Newforms` | 88219 | 59097 |

The checks that moved most (`hb` before, after; `report` lists them all):

| part | check | states | `hb` before | after |
|---|---|---|---:|---:|
| `Newforms` | `hLin3` | `rowsLinOk` (`linRowsOk`, `combOk`, `linAcc`, `unpackL`) | 15425 | 6089 |
| `Newforms` | `hNewDet` | `detOk` (the stacked product, `modOneOk`) | 3552 | 2074 |
| `Newforms` | `hMinor0` … `hMinor7` | `minorAtOk` (`minorOk`, `modRowsOk`, `modSlotsOk`, `modEntryOk`) | 3327 to 3338 | 1888 to 1891 |
| `Newforms` | `hNewTable` | `tableRowsOk` (`orbitSlotsOk`, `slotsEqOk`) | 10527 | 9386 |
| `Newforms` | `hMul3` | `mulCoordsOk` (`mulAccOk`, `accL`, `rootStep`, `stepL`) | 3641 | 2898 |
| `Newforms` | `hComp7` | `companionOk` (`compSlots`, `compSlotOk`) | 1575 | 857 |
| `Hecke` | `bigPrimes` | `isPrimeB` (`minFacFrom`) on every `p < 167` | 1444 | 808 |
| `Data` | `hpts` | `pointsKeyOk` (`pointKeyOk`, `p1Key`, `keyAt`) | 798 | 424 |
| `Data` | `hfac` | `facOk` | 347 | 72 |
| `Data` | `hWalk` | `cuspWalkOk` (`cuspWalk`, `genCuspOk`, `recPN`, `cuspPN`) | 2345 | 2113 |
| `Hecke` | `hTab` | `tabOk` | 525 | 321 |
| `Newforms` | `hTab0` … `hTab7` | `e2StackCheck` | 550 to 554 | 394 to 399 |
| `Newforms` | `hEig0` … `hEig7` | `e2RowsCheck` (its side conditions) | 2074 to 2093 | 1971 to 1989 |
| `QExp` | `hO1R` | `e2RowsCheck` | 4137 | 3955 |
| `Hecke` | `hStepQ2` | `colStepOkQ` | 3265 | 3123 |

The one-vector checks of `Hecke` (`hPs13_163`: 15030 both; `hP3` to `hP11`: 16 or 17 fewer) reach
the migrated definitions only through side conditions such as `rowsOk`, a small part of their work;
the checks of `Basis` do not move.

### What was not done

- `powSteps` and `rowSteps`, for the reason above.
- One level, one weight, one toolchain; levels 23, 39 and 37 were built, not measured.
- The term gate is not extended to the 84: their terms were meant to change, and the correctness
  test takes its place. No snapshot of their new terms was taken.
- `lake build Levels` and `lake exe axioms` were not run (the reviewer runs them); every proof is
  checked by the kernel, the test file included, with no `sorry`.

### To run it again

From the repository root, each line under the machine's lock:

```
lake env lean -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false scripts/bench/kernel_form/tests/Step4Eq.lean
REPEATS=3 SKIP_REPEATS=2 python3 scripts/bench/kernel_form/level_cost.py levels docs/bench/kernel_form/level_cost.jsonl TAG 2:997
python3 scripts/bench/kernel_form/step4_heartbeats.py run docs/bench/kernel_form/step4_heartbeats.jsonl TAG 2:997
python3 scripts/bench/kernel_form/level_cost.py report docs/bench/kernel_form/level_cost.jsonl before4 after4
python3 scripts/bench/kernel_form/step4_heartbeats.py report docs/bench/kernel_form/step4_heartbeats.jsonl before4 after4
```

## Step 5: three improvements of the compiler

Three changes to the compiler and to what it is given, and the two definitions step 4 left plain.
`Compute/KernelForm.lean` grew by 250 lines and lost 34 (`git diff --numstat`): about 160 for the
audit, 50 for the calls on a rebuilt constructor, 25 for the recursive fields, the rest its module
docstring. The kernel forms of the list functions are 100 lines of `Compute/Pack/Prim.lean`.

### The list functions of the core

After step 4 the kernel forms of the tree still called seven list functions of the core, which the
kernel unfolds through the core's own definitions: `List.getD` (through `Option` and `GetElem`) in
9 kernel forms (`colStepOk`, `colStepOkQ`, `frobProdOk`, `genOk`, `normOk`, `orbitSlotsOk`,
`pivotsOk`, `rootStep`, `zeroRowOk`); `List.tail` in 6 and `List.headD` in 5, through a matcher
(`accL`, `combOk`, `linRowsOk`, `slotsSignedOk`, `stepL`, and `frobProdOk` for `tail`);
`List.replicate` in 4 (`colMask`, `linRowsOk`, `mulRowOk`, `ones`), `List.range'` in 2
(`stepLevels`, `tabOk`), `List.eraseIdx` in `minorOk`, `List.filter` in `stepLevels`, through
`brecOn`. 20 kernel forms in all. `Compute/Pack/Prim.lean` (section `ListForms`) gives each
function a kernel form, a `kernel_def` with bare recursors (`listGetD`, `listHeadD`, `listTail`,
`listReplicate`, `listRange'`, `listEraseIdx`, `listFilter`), and a rule, the equation
`@List.getD α = listGetD`, …, proved by induction and marked `@[kernel_rule]`. The rules are global:
in every module that imports `Prim.lean`, the compiler writes the kernel form where a readable
definition calls the function of the core. Every module with such a call imported it already but
`Compute/P1KeyTab.lean` (`tabOk` walks `List.range'`), which now does. The readable sources do not
change, and `f.eq_src` proves each new kernel form equal to its readable definition.

`listGetD`, `listReplicate` and `listRange'` match in their body, so that the default, the
element and the step stay parameters and are not carried through the motive:

```
def listGetD.{u_1} : {α : Type u_1} → List α → ℕ → α → α :=
fun {α} l i d =>
  List.rec (motive := fun _ => ℕ → α) (fun i => d) (fun head tail tail_ih i => Nat.rec head (fun n n_ih => tail_ih n) i)
    l i
def zeroRowOk : ℕ → ℕ → ℕ → ℕ → List ℕ → Bool :=
fun K CY n k₀ Y => Bool.rec false ((listGetD Y k₀ (nat_lit 0)).beq (biasRow K CY n)) (CY.blt (pow2 K))
```

### `#kernel_audit`

`#kernel_audit` (section `Audit` of the compiler, and the command) reads the kernel form of every
`kernel_def` of the environment, or of the definitions named, and prints, per definition, what it
still contains, in two groups: the misses of the compiler (`ite`, `dite`, a matcher or `casesOn`,
`brecOn`, `WellFounded.fix`, `let`, `Decidable.decide`, an operation through an instance at a type
other than `ℤ`, a call of a list function of the core or of another function of a library, a call
of a readable definition `Src.g` or of an auxiliary one), and the representation it keeps (pairs,
`Int`). Each subterm is read once, types are not read. `#kernel_audit strict` is an error when a
miss is found. No file of the core runs it, so a build prints nothing more.

`scripts/bench/kernel_form/tests/Audit.lean` (the prototype's, replaced) imports every module of the
core and runs `#kernel_audit strict`, which passes:

```
kernel audit of 231: 0 with a miss of the compiler, 33 more with a representation it keeps
misses: none
representation: Int in 2 (4 subterms), pairs in 33 (83 subterms)
```

then lists the 33: the `PN` arithmetic and the weighing of `Walk.lean`, `checkPk`, `qorbit`,
`qappl`, `bdSelS`, `det1PN`, `facOk`, `p1Key`, … for pairs, `PN.val` and `cuspListOk` (`Int.gcd`)
for `Int`. The same file has four definitions with misses (a `dite`, `max`, a `where` helper) and a
`#guard_msgs` on the error of `#kernel_audit strict`. Run on the tree before this step, the audit
would have reported the 20 kernel forms above as misses (list function). It found one more while
this step was written: the first `powCells` matched its stage on `0`, `1` and a wildcard, which
Lean compiles with `if h : n = 1`, and its kernel form kept a `dite` and an `Eq.ndrec_symm`; the
last pattern is now `_ + 2`.

### The two rejections

The recursive fields of a constructor are now read off the recursor: `recFieldPositions` takes
the minor premises at a motive that is a variable, and each induction hypothesis names the field
it is about. The types of the fields were read before, after unfolding: the head of a cons of a
`List (SRow ℤ)` has the type `SRow ℤ`, an `abbrev` of a list, and was taken for a recursive field.
`innerQ` (`Compute/Pack/CheckQ.lean`), written with `List.foldr` for that reason, is again written
by pattern matching; its kernel form is identical to the one before (`compare-unmarked`), and one
proof (`innerQ_eq`) lost its `List.foldr_cons` and `← innerQ`.

A recursive call on a constructor rebuilt from the fields of a case is accepted. In the case
`x :: tail` of the recursion, a match that splits `tail` again into `y :: rows` is translated by
cases on `tail` whose proof carries the induction hypothesis on `tail` into each case, at the
constructor of the case: the call on `y :: rows` is then the induction variable at `tail`. The
split is the one `splitOn` made for overlapping patterns, with the hypothesis added to its motive;
a `casesOn` on a recursive field goes through it when it holds such a call. The constructor may be
written otherwise (`n + 1` after matching `n + 2` is `Nat.succ n`, found by `isDefEq`). No kernel
form of the tree changed: only calls the compiler rejected before take the new path.

`scripts/bench/kernel_form/tests/Accepts.lean` (new) holds what is now accepted: a recursion on a
`List Row` and on an `abbrev` of it, a walk two by two with overlapping patterns and without, a
recursion that calls itself on `n + 1` after matching `n + 2`; the kernel decides an `example` on
each. `tests/Rejects.lean` loses no case: `fib` still calls itself on `n` after matching `n + 2`.

### `rowSteps` and `powSteps`

`rowSteps` is a `kernel_def`, its text unchanged:

```lean
kernel_def rowSteps (K C p d τ Pl b : ℕ) : List ℕ → List ℕ → Bool
  | x :: y :: rows, q :: t :: W =>
    polyMulModOk K p d τ Pl (rowVal K C (Nat.add d 1) x) b (rowVal K C (Nat.add d 1) y) q t &&
      rowSteps K C p d τ Pl b (y :: rows) W
  | [], _ => true
  | [_], _ => true
  | _, _ => false
```

Its kernel form is a `List.rec` on the rows, with a `List.rec` on the tail in the case of a cons,
and `tail_ih` at the rest of `W` for the call on `y :: rows` (`docs/KERNEL_DEF.md`, "A call on a
rebuilt constructor").

`powSteps` recursed three cells down (`y :: q :: t :: W`), which no rewriting of the call reaches.
It is now read one cell at a time by `powCells`, which carries the cells of the triple read so far,
under its name with its arguments (`frobProdOk` and the statement of `powSteps_spec` do not
change):

```lean
kernel_def powCells (K p d τ Pl r : ℕ) : List ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | [], n, _, _, _, x, e => n == 0 && x == r && e == p
  | c :: W, 0, _, _, tags, x, e => powCells K p d τ Pl r W 1 c 0 tags x e
  | c :: W, 1, y, _, tags, x, e => powCells K p d τ Pl r W 2 y c tags x e
  | t :: W, _ + 2, y, q, tags, x, e =>
    polyMulModOk K p d τ Pl x (bif bitAt tags 0 then pow2 K else x) y q t &&
      powCells K p d τ Pl r W 0 0 0 (tags >>> 1) y (bif bitAt tags 0 then e + 1 else e + e)

kernel_def powSteps (K p d τ Pl r : ℕ) (W : List ℕ) (tags x e : ℕ) : Bool :=
  powCells K p d τ Pl r W 0 0 0 tags x e
```

Four lemmas restate the equations of the old definition (`powSteps_nil`,
`powSteps_cons_cons_cons`, `powSteps_singleton`, `powSteps_pair`, each `simp [powSteps,
powCells]`), and `powSteps_spec` uses them where it unfolded `powSteps`.

`scripts/bench/kernel_form/tests/Step5Eq.lean` (new) holds both definitions of `25f6d27`, verbatim,
in a namespace `Old`: `Step5Eq.rowSteps_eq : @Old.rowSteps = @rowSteps` (the plain definition is
the readable one by `kernel_rfl%`, the two being irreducible for the elaborator, then
`rowSteps.src_eq`), and `Step5Eq.powSteps_eq`, pointwise, by an induction on the list through the
four lemmas. It compiles without an error or a `sorry`.

### The proofs

No statement changed. The kernel forms that now call `listGetD`, `listReplicate`, … are no longer
definitionally equal to their readable definitions on a variable list, and four proofs of the tree
used that: `ones_succ` (`Compute/Pack/Walk.lean`) rewrites back with `← ones`; `stepLevelsQ_eq`
(`Compute/PackedColumnQ.lean`) rewrites `stepLevels` first; `length_stepL` and `mulRowOk_spec`
(`Forms/Newform/Compute/Operator.lean`) rewrite with `stepL` and `mulRowOk` instead of unfolding
them by unification. With `innerQ_eq` and `powSteps_spec` above, six proofs changed.

`tests/Step4Eq.lean`: eight of its 84 theorems were `rfl` against a kernel form that now calls a
list form. `ones`, `colMask`, `stepLevels`, `zeroRowOk`, `normOk` are proved through the readable
definition (`Old.f = Src.f` by `rfl`, then `f.src_eq`); `mulRowOk`, `rootStep`, `minorOk`, whose
readable definitions call readable definitions that are irreducible, by `rw [f]` and `rfl`.

### The builds and the gates

The core builds without a warning (`lake build`, 9445 jobs), `check_imports.py` passes, and the
level targets build as they are (levels 23 and 997 of weight 2, five parts each, level 39 of
weight 2 and level 37 of weights 4 and 6, four parts each: 9461 jobs, no warning). The tests behave
as their headers say: `Accepts`, `Audit`, `Shapes`, `Syntax`, `Step4Eq`, `Step5Eq` compile with no
error, `Faults` and `Rejects` give the errors they list and no other. The term gates print, line for
line, what they printed before the first edit (`compare docs/bench/kernel_form/snapshot_364e70a`,
`compare-unmarked docs/bench/kernel_form/snapshot_unmarked`, both exit 0): no definition of the
snapshots calls a list function of the core, and `innerQ` is identical.

### The cost gate

`REPEATS=3 SKIP_REPEATS=2 level_cost.py levels docs/bench/kernel_form/level_cost.jsonl TAG 2:997`,
tags `before5` (the tree before the first edit of this step) and `after5`:

| part | kernel G before | after | full G before | after | peak GB before | after |
|---|---:|---:|---:|---:|---:|---:|
| weight 2, 997, `Data` | 3.338 | 3.351 | 20.209 | 20.210 | 0.402 | 0.401 |
| weight 2, 997, `Basis` | 5.349 | 6.142 | 25.250 | 25.176 | 0.431 | 0.427 |
| weight 2, 997, `Hecke` | 25.182 | 22.841 | 52.494 | 50.752 | 0.733 | 0.733 |
| weight 2, 997, `QExp` | 3.371 | 2.983 | 27.033 | 26.646 | 0.548 | 0.546 |
| weight 2, 997, `Newforms` | 46.151 | 41.492 | 82.567 | 77.291 | 0.756 | 0.688 |
| all five | 83.391 | 76.809 | 207.553 | 200.075 | 0.756 | 0.688 |

`Newforms` loses 10 % of its kernel work and 0.07 GB of peak, `Hecke` 9 %, `QExp` 12 %; `Data`
does not move. `Basis` reads 0.8 G higher and is noise: its full runs fell (25.250, 25.503, 25.812
before; 25.177, 25.176, 25.194 after), the runs without the kernel fell more (20.462, 19.901
before; 19.044, 19.034 after), its `hb` fell by 14, and after step 4 its kernel figure was 6.152.

`step4_heartbeats.py run docs/bench/kernel_form/step4_heartbeats.jsonl TAG 2:997`, the same tags:
of the 128 checks, 69 fall, 59 do not move, none rises.

| part | `hb` before | after |
|---|---:|---:|
| `Data` | 4014 | 4014 |
| `Basis` | 10337 | 10323 |
| `Hecke` | 37735 | 34360 |
| `QExp` | 5147 | 4416 |
| `Newforms` | 59097 | 51008 |

The checks that moved most:

| part | check | through | `hb` before | after |
|---|---|---|---:|---:|
| `Newforms` | `hNewTable` | `orbitSlotsOk` (`List.getD`) | 9386 | 3791 |
| `Hecke` | `hStepQ2` | `colStepOkQ` (`E.getD`: `List.getD`), `e2StackCheck` (`ones`: `List.replicate`) | 3123 | 1201 |
| `Newforms` | `hMul3` | `rootStep`, `stepL`, `accL` (`List.getD`, `List.headD`, `List.tail`), `mulRowOk` (`List.replicate`) | 2898 | 1794 |
| `QExp` | `hEch` | `pivotsOk` (`List.getD`) | 1117 | 400 |
| `Hecke` | `hStepQ3`, `hStepQ5`, `hStepQ7`, `hStepQ11` | as `hStepQ2` | 1163, 538, 424, 273 | 525, 290, 247, 187 |
| `Hecke` | `hTab` | `tabOk` (`List.range'`) | 321 | 160 |
| `Newforms` | `hMinor0` … `hMinor7` | `minorOk` (`List.eraseIdx`), `zeroRowOk` (`List.getD`), `e2StackCheck` (`ones`) | 1888 to 1891 | 1801 to 1804 |
| `Newforms` | `hFrob3` … `hFrob7` | `frobProdOk` (`List.getD`, `List.tail`), `powSteps`, `rowSteps` | 35 to 196 | 28 to 148 |
| `Newforms` | `hTab0` … `hTab7` | `e2StackCheck` (`ones`: `List.replicate`) | 394 to 399 | 353 to 357 |
| `Newforms` | `hLin3` | `linRowsOk`, `combOk` (`List.replicate`, `List.headD`, `List.tail`) | 6089 | 6054 |
| `Newforms` | `hNewDet` | `detOk` (`e2StackCheck`: `ones`) | 2074 | 2053 |

`hLin3` and `hNewDet` move little: their work is in the products of packed rows, not in the list
functions.

### What was not done

- One level, one weight, one toolchain; levels 23, 39 and 37 were built, not measured.
- The audit reports calls of plain definitions of the project (not `kernel_def`s) as nothing: they
  are the author's choice, as calls of other kernel forms are. It reads a kernel form, not the
  definitions it calls.
- No snapshot of the new terms was taken for the term gate; `Step5Eq.lean` and the audit take its
  place for the definitions this step changed.
- `lake build Levels` and `lake exe axioms` were not run (the reviewer runs them).

### To run it again

From the repository root, each line under the machine's lock:

```
lake env lean -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false scripts/bench/kernel_form/tests/Audit.lean
lake env lean -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false scripts/bench/kernel_form/tests/Accepts.lean
lake env lean -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false scripts/bench/kernel_form/tests/Step5Eq.lean
python3 scripts/bench/kernel_form/level_cost.py report docs/bench/kernel_form/level_cost.jsonl before5 after5
python3 scripts/bench/kernel_form/step4_heartbeats.py report docs/bench/kernel_form/step4_heartbeats.jsonl before5 after5
```

## Step 6: the checks of weights 4 and 6

A walk of the compiled environment from every theorem the levels prove by `decide +kernel` found
29 ordinary `def`s still evaluated, all used by the levels of weights 4 and 6. They were to become
`kernel_def`s under their names, with their arguments in their order (`Levels/` was not
regenerated):

- `Compute/PackedMul`: `absSumN`;
- `Compute/Pack/Kronecker`: `slotsLe`;
- `Compute/Pack/HeckeImg`: `checkOnePk`, `innerPackT`, `phiPackPk`, `phiPkOk`;
- `Compute/Pack/Weight`: `coeffT`, `coeffTT`, `relRowS`, `relRowT`, `relRowW`, `sgnNat`;
- `Compute/Pack/PlusImgW`: `bdRowW`, `colsOk`, `killCheck`, `relKillsW`, `starCheckW`, `starRowW`,
  `starTgtW`;
- `Compute/Pack/HeckeKey`: `heckeRowKey`, `keyedCons`;
- `Compute/Pack/HeckeKeyW`: `heckeRowAtW`, `heckeRowW`, `heilbronnBoundW`, `keyedPolyCons`,
  `linMulAux`, `linPow`, `polyEntries`, `polyPow`.

Not in scope: `heilbronnRaw` and `cuspInvPair`, in `Theory/` (which may not import `Compute/`), and
the library forms only the acceptance files evaluate.

All 29 are `kernel_def`s. Their bodies are written in notation (`a % (w + 1) = w`, `t < pow2 (S *
g)`, `lenN ΦT == n`, `if`, `p.fst`, `p.snd`, `fun x ↦`); none was rejected and none is left.
`phiPkOk` loses its `noncomputable`, which it no longer needs: `lenN` and the other kernel forms it
calls are computable through their `csimp` lemmas. Pairs and `Int` stay. 24 of the 29 carry the
comment `-- TODO: kernel form: …` naming what is left, as the earlier ones do: the pairs (`colsOk`,
`killCheck`, `relKillsW`, `linMulAux`, `linPow`, `polyPow`, `keyedPolyCons`), pairs with `Int`
entries (`absSumN`, `relRowS`, `relRowT`, `bdRowW`, `starRowW`, `keyedCons`, `polyEntries`), an
`Int` result (`sgnNat`, `coeffT`, `coeffTT`), an `Int` argument (`checkOnePk`, `starTgtW`,
`starCheckW`), and the `Int` matrices (`heckeRowKey`, `heckeRowW`, `heckeRowAtW`,
`heilbronnBoundW`). The other five (`slotsLe`, `phiPackPk`, `phiPkOk`, `innerPackT`, `relRowW`)
compute on naturals and lists of naturals only.

### Four library functions given kernel forms

Written in notation, four of the bodies call functions of a library that had no kernel form:
`relRowT` calls `List.range` and `++`, `bdRowW` calls `++`, `starCheckW` calls `List.zip`, and
`coeffT`, `coeffTT` call `Nat.choose`. The compiler keeps such a call, the kernel unfolds it
through the library's definition at every use, and `#kernel_audit strict` reports it as a miss, so
`tests/Audit.lean` would fail. Each was given a kernel form and a `@[kernel_rule]`, as step 5 did
for `List.getD` and the others:

- `Compute/Pack/Prim.lean`, section `ListForms`: `listAppend` (the second list a parameter, not
  carried through the motive) with `append_eq_listAppend : as ++ bs = listAppend as bs`,
  `listZip` with `zip_eq_listZip : @List.zip α β = listZip`, and
  `range_eq_listRange' : List.range n = listRange' 0 n 1`, which needs no new kernel form;
- `Compute/Pack/Weight.lean`, section `BinomialBlocks`: `natChoose`, Pascal's rule by structural
  recursion on `n`, with `choose_eq_natChoose : Nat.choose = natChoose`. It is in `Weight.lean`,
  not `Prim.lean`, because `Prim.lean` does not import `Nat.choose`; the rule applies in every
  module that imports `Weight.lean`.

The readable bodies keep `List.range`, `++`, `zip` and `choose`; the kernel forms call
`listRange'`, `listAppend`, `listZip`, `natChoose`. No kernel form of an earlier definition calls
one of the four (the audit passed before this step), so no earlier term changed: the term gates
below confirm it.

```
def relRowT : ℕ → ℕ → ℕ → ℕ → ℕ → SRow ℤ :=
fun w p i τp ττp =>
  listAppend
    ((blkIdx w p i, 1) ::
      List.rec [] (fun a x ih => (blkIdx w τp a, coeffT w i a) :: ih)
        (listRange' (nat_lit 0) (w.add (nat_lit 1)) (nat_lit 1)))
    (List.rec [] (fun a x ih => (blkIdx w ττp a, coeffTT w i a) :: ih)
      (listRange' (nat_lit 0) (w.add (nat_lit 1)) (nat_lit 1)))
def coeffT : ℕ → ℕ → ℕ → ℤ :=
fun w i j => Bool.rec 0 (sgnNat (w.sub j) (natChoose i ((i.add j).sub w))) (w.ble (i.add j))
```

### The correctness test

`scripts/bench/kernel_form/tests/Step6Eq.lean` (new) holds the 29 replaced definitions verbatim
from `git show 4c93dce:<file>`, in a namespace `Old` of their own namespace, callers first and the
files from the last to the first (`starRowW` calls `sgnNat`), so that every name in a body but the
definition itself resolves to the definition of the tree; for each, `Step6Eq.f_eq : @Old.f = @f`
or its pointwise form. It compiles without an error, a warning or a `sorry`.

- `rfl` (8): `slotsLe`, `checkOnePk`, `relRowS`, `killCheck`, `relKillsW`, `starRowW`,
  `heckeRowAtW`, `polyPow`.
- `kernel_rfl%` (5): `relRowW`, `sgnNat`, `starTgtW`, `keyedCons`, `keyedPolyCons`: a `bif` (and,
  in `starTgtW`, two `let`s) against a `Bool.rec`, equal for the kernel, not for the elaborator.
- `rw [f]` and then `rfl` against the readable body (6): `phiPkOk`, `phiPackPk`, `innerPackT`,
  `relRowT`, `starCheckW`, `colsOk`: the plain definition calls `List.map`, `List.all` (and
  `List.range`, `++`, `List.zip`), the kernel form a `List.rec` (and the list forms).
- `simp` with the equations of both (3): `coeffT`, `coeffTT`, `bdRowW`: the kernel form calls
  `natChoose` or `listAppend` where the plain definition calls `Nat.choose` or `++`, so the two
  are not equal by unfolding; the readable equation calls the library function, and `simp` reads
  the `bif Nat.ble …` of the plain definition as the `if … ≤ …` of the readable one.
- an induction with the readable equations (7): the recursive definitions, `absSumN`,
  `heckeRowKey`, `heckeRowW`, `polyEntries`, `linPow`, `linMulAux`, `heilbronnBoundW` (a structural
  recursion through `brecOn` against a bare recursor).

So `rfl` was not enough for 21 of the 29, `kernel_rfl%` included.

### The proofs

No statement changed. The proofs that broke named the old heads in a `simp only` or a `rw`
(`Nat.blt_eq`, `Nat.beq_eq`, `Nat.add_eq`, `Nat.sub_eq`, `Bool.cond_eq_ite`, `natDiv_eq`, …), which
the readable equations no longer contain, or unfolded a check by unification through the plain
definition:

- `Compute/PackedMul`: `absSumN_eq` (drops `Nat.add_eq`);
- `Compute/Pack/Walk`: `absFields_eq` (adds `Nat.add_eq`: `absFields_succ` states `Nat.add`, the
  readable `absSumN` a `+`);
- `Compute/Pack/Kronecker`: `slotsLe_iff` (`decide_eq_true_eq` in place of the old heads);
- `Compute/Pack/HeckeImg`: `isImg_of_phiPkOk` (`beq_iff_eq` for `Nat.beq_eq`);
- `Compute/Pack/CheckQ`: `checkOneQ_eq` ends with `rfl`: after its rewrites the two sides differ by
  `Nat.blt t b` against `decide (t < b)`, equal by unfolding, which the `rfl` of `rw` (at reducible
  transparency) does not see;
- `Compute/Pack/Weight`: `sgnNat_eq`, `binomCoeff_tau` (`rw [f]`), `binomCoeff_tauSq`,
  `decodeAt_relRowW`, `packRow_relRowW_zero` (fewer `simp` arguments);
- `Compute/Pack/PlusImgW`: `decodeAt_bdRowW`, `decodeAt_starRowW` (fewer `simp` arguments),
  `colsOk_spec` (`rw [colsOk] at h`, then one `simpa`), `val_starTgtW` and `starCheckW_getD` (the
  term they were, after `rw [starTgtW]` or `rw [starCheckW] at h`: the lemma they apply is stated
  on the plain body, which the elaborator no longer reaches by unfolding the kernel form);
- `Compute/Pack/HeckeKey`: `keyedCons_eq` (`rw [keyedCons]`: its statement is the readable body);
- `Compute/Pack/HeckeKeyW`: `keyedPolyCons_eq` (likewise), `absSumN_polyEntries_le`,
  `decodeAt_polyEntries`, `mem_polyEntries` (a split on `q.fst = q.snd` in place of `cases` on
  `Nat.beq`), `absSum_heckeRowW_le` (`simpa` through `pow_mul_pow_le_max_pow`, whose statement
  keeps its `bif Nat.ble`), `decodeAt_heckeRowW`, `mem_heckeRowW` (drop `Nat.sub_eq`).

23 proofs in 9 files. No file of `Cert/` or `Forms/` changed.

Docstrings: the module docstring of `PackedMul` said that `packNat`, `unpackNat`, `absSum` are
written with explicit `Nat` heads; it now says that `packNat` and `absSumN` are `kernel_def`s
evaluated with them. `Weight` lists `natChoose`, `Prim` the two new list forms.

### The builds and the gates

Each module was built after its migration (with `CheckQ` and `Quotient`, whose proofs unfold
`checkOnePk`, `innerPackT` and `heckeRowKey`), then the core once: `lake build`, 9445 jobs, no
warning. `check_imports.py` passes. The level targets build as they are: level 37 of weights 4
and 6, level 5 of weight 4 and level 3 of weight 6 (four parts each), levels 997 and 23 of weight 2
(five parts each), 9469 jobs, no warning. The term gates print, line for line, what they printed
before the first edit (`compare docs/bench/kernel_form/snapshot_364e70a`, `compare-unmarked
docs/bench/kernel_form/snapshot_unmarked`, both exit 0): no definition of the snapshots calls one of
the four library functions. `tests/Audit.lean` passes:

```
kernel audit of 263: 0 with a miss of the compiler, 55 more with a representation it keeps
misses: none
representation: Int in 11 (16 subterms), pairs in 52 (129 subterms)
```

(231 kernel forms before, 33 with a representation: the 29 of this step and the three new kernel
forms make 263, and 21 of the 29 and `listZip` keep pairs or `Int`). `Step4Eq`, `Step5Eq`,
`Step6Eq` and `Accepts` compile with no error and no warning. The new theorems and the changed
proofs rest on `propext`, `Classical.choice`, `Quot.sound` at most.

### The cost gate

`REPEATS=3 SKIP_REPEATS=2 level_cost.py levels docs/bench/kernel_form/level_cost.jsonl TAG 4:37 6:37
2:997`, tags `before6` (the tree before the first edit of this step) and `after6`, on
`v4.37.0-rc1`:

| part | kernel G before | after | full G before | after | peak GB before | after |
|---|---:|---:|---:|---:|---:|---:|
| weight 4, 37, `Data` | 0.134 | 0.139 | 16.892 | 16.876 | 0.336 | 0.336 |
| weight 4, 37, `Basis` | 5.199 | 3.874 | 22.995 | 21.246 | 0.387 | 0.372 |
| weight 4, 37, `Hecke` | 3.657 | 2.990 | 24.615 | 23.935 | 0.437 | 0.412 |
| weight 4, 37, `QExp` | 0.806 | 0.205 | 21.425 | 20.813 | 0.387 | 0.387 |
| weight 4, 37, all four | 9.796 | 7.208 | 85.927 | 82.870 | 0.437 | 0.412 |
| weight 6, 37, `Data` | 0.171 | 0.135 | 16.922 | 16.886 | 0.336 | 0.337 |
| weight 6, 37, `Basis` | 18.398 | 12.625 | 35.989 | 30.214 | 0.528 | 0.533 |
| weight 6, 37, `Hecke` | 8.883 | 6.909 | 30.637 | 28.650 | 0.691 | 0.610 |
| weight 6, 37, `QExp` | 0.240 | −0.872 | 20.902 | 20.699 | 0.388 | 0.388 |
| weight 6, 37, all four | 27.692 | 18.797 | 104.450 | 96.449 | 0.691 | 0.610 |
| weight 2, 997, `Data` | 3.048 | 3.815 | 20.172 | 20.652 | 0.405 | 0.405 |
| weight 2, 997, `Basis` | 5.423 | 6.158 | 25.138 | 25.158 | 0.430 | 0.428 |
| weight 2, 997, `Hecke` | 23.487 | 23.315 | 50.767 | 50.596 | 0.732 | 0.732 |
| weight 2, 997, `QExp` | 3.004 | 3.022 | 26.634 | 26.635 | 0.546 | 0.548 |
| weight 2, 997, `Newforms` | 41.463 | 41.496 | 77.247 | 77.276 | 0.696 | 0.694 |
| weight 2, 997, all five | 76.425 | 77.806 | 199.958 | 200.317 | 0.732 | 0.732 |

At level 37, `Basis` loses 25 % of its kernel work in weight 4 and 31 % in weight 6, `Hecke` 18 %
and 22 %, and the peak of `Hecke` in weight 6 falls by 0.08 GB: the whole level costs 7.2 G of kernel
work instead of 9.8 in weight 4, 18.8 instead of 27.7 in weight 6. The full runs agree (−1.7 and
−5.8 G for `Basis`, −0.7 and −2.0 G for `Hecke`), and so do the heartbeats below.

Four kernel figures are noise of the meter. The `QExp` parts of level 37 name none of the 29
definitions, and their `hb` does not move (128 and 175); their kernel work is below the meter's
resolution, the difference of a full run and a run without the kernel that differ by up to 1.4 G
from one run to the next (weight 6: runs without the kernel 20.662, 22.077 before; 21.571, 22.117
after; hence a negative figure). At level 997, `Data` and `Basis` read 0.8 and 0.7 G higher with
an `hb` identical to the unit (4014 and 10323): `Data` ran 20.389, 20.180, 20.172 in full and
17.124, 18.157 without the kernel before, 21.607, 21.156, 20.652 and 16.837, 16.848 after;
`Basis` 25.141, 25.145, 25.138 and 19.715, 19.746 before, 25.158, 26.581, 26.229 and 19.000,
20.438 after (step 5 saw the same part read 5.3 to 6.2 G). `Hecke` and `Newforms` of 997 are
within noise; `Hecke` gains one check, below.

`step4_heartbeats.py run docs/bench/kernel_form/step4_heartbeats.jsonl TAG K:N` on the three
levels, the same tags: of the 228 checks, 25 fall, 203 do not move, none rises.

| part | `hb` before | after |
|---|---:|---:|
| weight 4, 37, `Data` | 264 | 264 |
| weight 4, 37, `Basis` | 8088 | 5150 |
| weight 4, 37, `Hecke` | 4666 | 3581 |
| weight 4, 37, `QExp` | 128 | 128 |
| weight 6, 37, `Data` | 264 | 264 |
| weight 6, 37, `Basis` | 24857 | 15275 |
| weight 6, 37, `Hecke` | 11673 | 8609 |
| weight 6, 37, `QExp` | 175 | 175 |
| weight 2, 997, `Data` | 4014 | 4014 |
| weight 2, 997, `Basis` | 10323 | 10323 |
| weight 2, 997, `Hecke` | 34360 | 34195 |
| weight 2, 997, `QExp` | 4416 | 4416 |
| weight 2, 997, `Newforms` | 51008 | 51008 |

The checks that moved most (the same checks of weight 4 move by a similar fraction):

| level | check | states | `hb` before | after |
|---|---|---|---:|---:|
| 6, 37 | `hHecke` | `phiPkOk`, `heilbronnBoundW` at eight primes, `checkPk` on the image rows (`heckeRowAtW`, `heckeRowW`, `keyedPolyCons`, `polyPow`, `linPow`, `linMulAux`, `polyEntries`; `innerPackT`) | 10304 | 7240 |
| 6, 37 | `hStarP`, `hStarM` | `starCheckW` (`starTgtW`, `listZip`) on the relation and star columns (`relRowW`, `relRowS`, `relRowT`, `coeffT`, `coeffTT`, `natChoose`, `sgnNat`, `starRowW`) | 5969, 5393 | 3432, 3118 |
| 6, 37 | `hColsR` | `colsOk` on the relation columns (`absSumN`, `relRowW` …) | 3151 | 1197 |
| 4, 37 | `hHecke` | as in weight 6 | 3868 | 2783 |
| 6, 37 | `hDualP`, `hDualM` | `dualCheckW` (`relKillsW`, `relRowW` …) | 2697, 2652 | 1693, 1647 |
| 4, 37 | `hColsR` | as in weight 6 | 1366 | 533 |
| 6, 37 | `hRankR` | `rankCheckW` on the relation columns | 2173 | 1839 |
| 997 | `hP2` | `checkPkH` at `p = 2` on the rows of `heckeRowsOn` (`heckeRowKey`, `keyedCons`); the other primes read theirs through `qrowsOn` | 2582 | 2417 |
| 6, 37 | `hColsB`, `hColsS` | `colsOk` on the boundary and star columns (`bdRowW`, `listAppend`; `starRowW`) | 260, 225 | 110, 108 |
| 6, 37 | `hCuspP`, `hCuspM` | `killCheck` on the boundary columns | 280, 275 | 177, 173 |

`hRankB` falls by 1 at both weights; nothing else moves. The `Newforms` of 997 does not move to the
unit: it reaches `slotsLe` only through `polyMulModOk` in its Frobenius checks (`hFrob3` …), six
tests a product, whose kernel form changed by `Bool.rec` in place of `&&`, below the unit of `hb`
(a thousand allocations).

### What was not done

- Pairs and `Int` stay, as the brief asked (another agent studies pair splitting): 21 of the 29
  kernel forms keep pairs or `Int`, and `starCheckW` builds the nested pairs of `listZip W (listZip
  V Ds)` before walking them, where a walk of the three lists in step would not.
- `linMulAux` and `polyEntries` carry an argument through the motive (`prev`, which changes at
  each step, and `r`, which does not): their pattern matching was kept as written; a `match` in the
  body would make `r` a parameter, as `listAppend`'s second list is.
- One level a weight, one toolchain; level 5 of weight 4, level 3 of weight 6 and level 23 were
  built, not measured.
- The term gate is not extended to the 29: their terms were meant to change, and the correctness
  test takes its place. No snapshot of their new terms was taken.
- `lake build Levels` and `lake exe axioms` were not run (the reviewer runs them); every proof is
  checked by the kernel, the test file included, with no `sorry`.

### To run it again

From the repository root, each line under the machine's lock:

```
lake env lean -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false scripts/bench/kernel_form/tests/Step6Eq.lean
lake env lean -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false scripts/bench/kernel_form/tests/Audit.lean
REPEATS=3 SKIP_REPEATS=2 python3 scripts/bench/kernel_form/level_cost.py levels docs/bench/kernel_form/level_cost.jsonl TAG 4:37 6:37 2:997
python3 scripts/bench/kernel_form/step4_heartbeats.py run docs/bench/kernel_form/step4_heartbeats.jsonl TAG 4:37
python3 scripts/bench/kernel_form/step4_heartbeats.py run docs/bench/kernel_form/step4_heartbeats.jsonl TAG 6:37
python3 scripts/bench/kernel_form/step4_heartbeats.py run docs/bench/kernel_form/step4_heartbeats.jsonl TAG 2:997
python3 scripts/bench/kernel_form/level_cost.py report docs/bench/kernel_form/level_cost.jsonl before6 after6
python3 scripts/bench/kernel_form/step4_heartbeats.py report docs/bench/kernel_form/step4_heartbeats.jsonl before6 after6
```

## Pair splitting

### The question

A signed value is a pair of naturals (`PN`, `Compute/Pack/Walk.lean`), and the compiler kept pairs
as they were written: 33 kernel forms of the core built or projected them (`#kernel_audit`). A pair
and its projection cost about 12.9 k instructions a use inside a loop (`docs/CFSG_EXPERIMENTS.md`,
E14). The hand-written fast forms of weight 2 had split their pairs by hand, a pair-valued walk
becoming two walks, one a component (`wP`, `wQ`, `oP`, `oQ` in `Compute/Pack/CheckQ.lean`). Does
splitting the pair-valued kernel forms into component walks make the certificates cheaper, and if
it clearly does, can `kernel_def` do it?

### The answer

Not for walks. A pair-valued walk split into one walk a component costs the checks of weights 4
and 6 3.6 to 21.3 % more kernel instructions, 8 to 70 % more allocations, at an equal or higher
peak, and their parts 5.1 to 11.0 % more (the variant `S` below). Keeping each walk's result a pair
and splitting every other pair (the variant `R`) is no better: −1.1 to +3.2 % on the checks of
`Basis`, +10.9 % on `hHecke`. What gains is the arithmetic on pairs that no walk carries: the cusp
check (`genCuspOk`, `det1PN`, `recPN`, `cuspPN`, `PN.mul`, …) costs 10.1 to 10.2 % less on `hWalk`
at 997 and the part `Data` of 997 6.0 % less (3.335 against 3.133 G), at the same peak. That
passes the rule set for building a pass (5 % of the kernel instructions of one part, or 10 % on the
checks it touches, with no worse peak) for that case only, so the pass was built for that case
only: `kernel_def` now gives a definition on pairs of naturals that walks no pair-valued data
component forms, and compiles the definitions that follow on them; a walk with a pair result, a
pair-valued function argument, a list of pairs and a pair of another type are kept. With the pass,
the part `Data` of 997 costs 5.9 % less (3.352 against 3.154 G, `hWalk` 4.9 % fewer allocations),
and every other part of levels 37, 997 and 23 costs the same, to the noise of the meter.

The pass is not in the compiler: the owner's decision, on these figures. 0.2 G of the 76.8 G of
level 997 does not pay for about 230 lines of metaprogramming, which also add 0.3 to 0.5 % of
allocations to `hHecke` at weights 4 and 6. Phase 2 below is the record of what the pass did; the
pass itself is kept as `scripts/bench/kernel_form/pair_pass.patch` (the compiler, one proof of
`Cert/Basis/WeightTwo.lean`, one proof of `tests/Step4Eq.lean`, and its test `tests/Pairs.lean`),
which applies at commit `4c93dce`.

The kernel caches a value by its term. A pair-valued walk is reduced once, and the second
component of its result, and of every step, is found again by term; two component walks make every
step twice: the recursor's step, the instantiation of its minor premise, the test of the sign bit
(found again by term), each application of the scaled read `sc`. That costs more than the pairs
they remove. A pair-valued function argument split into two (`wP`, `wQ`) is applied twice at every
use, which is what `R` loses on `hHecke` (nested closures: the scaled read, the source `w`, the
generated column). In arithmetic that walks nothing each component is computed once either way,
and splitting removes only the pairs and their projections.

### Phase 1: the method

`scripts/bench/kernel_form/pair_ab.py`, on the model of `plain_ab.py`; the sources are those of
the worktree at `4c93dce`, and nothing of the core changes in phase 1.

- `PairSplit/SplitDefs.lean` (beside the script, compiled into a scratch library by `pair_ab.py
  lib`): the pair-valued kernel forms that the checks of weights 4 and 6 and the cusp walk reach,
  split by hand into component walks, each a `kernel_def`, mirroring the pair forms call for call:
  `weighFields`, `addField`, `weighPk`, `packPk`, `weighPkPN`, `weighPkSlot`, `weighPN`, `packPN`,
  `weighSlot`, `smulSlot`, `readPN`, `recPN`, `cuspPN`, the `PN` operations, `fitsPN`, `stackPN`,
  `rowsCheck`, and twins with the suffix `S` of the checks the levels name: `killCheck`,
  `starCheckW` (with `starTgtW`), `dualCheckW` (with `relKillsW`), `rankCheckW`, `phiPkOk`,
  `checkPk` (with `innerPackT`), `checkOnePk`, `cuspWalkOk` (with `genCuspOk`, `det1PN`). A call of
  a pair form `f` becomes a call of `fP` or `fQ`, a pair argument two naturals, a pair-valued
  function argument `w : ℕ → PN` two, `wP wQ : ℕ → ℕ`; a list of pairs mapped and consumed
  (`ΦT.map (packPk …)` in `dualCheckW`) is fused with its consumer. `PairSplit/SplitEq.lean` proves
  every component walk the projection of its pair walk (`weighFields_fst`, …) and every twin the
  check of the tree (`dualCheckWS_eq`, …), with no `sorry`.
- `PairSplit/KeepRec.lean`, the variant `R`: every walk keeps its pair result, built in each step
  from the components of the step (`addFieldP`, `smulSlotP`, …) and the projections of the
  recursive call, the same term in both; its pair-valued function arguments are split and its
  callers project it. The twins have the suffix `R` (the cusp walk is that of `S`).
- `pair_ab.py checks`: one check of a part, stated `copies` times (README "the meter's noise"), in a
  file that imports the built part, on the pair forms (`U`) and on the twins; each file 3 times in
  full and 2 times without the kernel, the variants in turn; `hb` of one copy.
- `pair_ab.py prepare`, `build`, `measure`, `heartbeats`: the parts of levels 37 (weights 4 and 6)
  and 997 in two libraries of their own: `U` the level files with `import PairSplit.SplitEq`
  added, `S` the same with every check that names a twin proved on it (`simp only [← XS_eq]`, then
  `decide +kernel`). The level files and their data are those of the repository. In `S` the
  statements of the levels are unchanged, and `hb` counts the elaboration of the `simp only` too
  (6 on `hWalk` at 37).
- Apple M5, 32 GB, shared with a second agent, one heavy job at a time.

### Phase 1: the checks

Kernel G, `hb` of one copy, peak GB (`pair_checks.jsonl`; the first batch ran on the same sources
compiled as the module `PairPilot.SplitDefs`, the second through `pair_ab.py checks`):

| check | copies | twin | kernel G `U` | twin | twin − `U` | `hb` `U` | twin | peak `U` | twin |
|---|---:|---|---:|---:|---:|---:|---:|---:|---:|
| weight 4, 37, `hDualP` | 8 | `S` | 6.374 | 6.701 | +5.1 % | 1144 | 1241 | 0.371 | 0.375 |
| weight 4, 37, `hStarP` | 8 | `S` | 6.357 | 6.731 | +5.9 % | 1158 | 1290 | 0.369 | 0.371 |
| weight 4, 37, `hRankR` | 10 | `S` | 7.155 | 7.413 | +3.6 % | 915 | 1297 | 0.392 | 0.393 |
| weight 4, 37, `hCuspP` | 40 | `S` | 2.543 | 2.791 | +9.8 % | 135 | 151 | 0.341 | 0.341 |
| weight 6, 37, `hDualP` | 4 | `S` | 8.099 | 8.584 | +6.0 % | 2710 | 2993 | 0.448 | 0.453 |
| weight 6, 37, `hStarP` | 2 | `S` | 8.552 | 9.090 | +6.3 % | 5983 | 6832 | 0.507 | 0.519 |
| weight 6, 37, `hRankR` | 4 | `S` | 7.967 | 9.667 | +21.3 % | 2186 | 3726 | 0.486 | 0.493 |
| weight 4, 37, `hHecke` | 3 | `S` | 7.302 | 8.279 | +13.4 % | 3867 | 4435 | 0.436 | 0.452 |
| weight 6, 37, `hHecke` | 1 | `S` | 7.095 | 8.036 | +13.3 % | 10297 | 11920 | 0.687 | 0.726 |
| weight 2, 997, `hWalk` | 5 | `S` | 8.610 | 7.731 | −10.2 % | 2121 | 1986 | 0.397 | 0.393 |
| weight 4, 37, `hDualP` | 8 | `R` | 6.359 | 6.449 | +1.4 % | 1144 | 1169 | 0.371 | 0.372 |
| weight 4, 37, `hStarP` | 8 | `R` | 6.353 | 6.311 | −0.7 % | 1158 | 1161 | 0.368 | 0.368 |
| weight 4, 37, `hRankR` | 10 | `R` | 7.190 | 7.404 | +3.0 % | 915 | 958 | 0.391 | 0.392 |
| weight 4, 37, `hCuspP` | 40 | `R` | 2.554 | 2.596 | +1.6 % | 135 | 138 | 0.341 | 0.341 |
| weight 6, 37, `hDualP` | 4 | `R` | 8.087 | 8.223 | +1.7 % | 2710 | 2777 | 0.443 | 0.446 |
| weight 6, 37, `hStarP` | 2 | `R` | 8.566 | 8.468 | −1.1 % | 5983 | 5968 | 0.506 | 0.506 |
| weight 6, 37, `hRankR` | 4 | `R` | 7.964 | 8.220 | +3.2 % | 2186 | 2303 | 0.487 | 0.489 |
| weight 4, 37, `hHecke` | 3 | `R` | 7.295 | 8.091 | +10.9 % | 3867 | 4286 | 0.436 | 0.448 |
| weight 6, 37, `hHecke` | 1 | `R` | 7.088 | 7.861 | +10.9 % | 10297 | 11485 | 0.688 | 0.716 |
| weight 2, 997, `hWalk` | 5 | `S` | 8.600 | 7.732 | −10.1 % | 2121 | 1986 | 0.398 | 0.392 |

The full runs of a file agree to 0.02 G but for one run in three that reads 1.2 to 1.4 G higher
(the modes of the meter, README "the meter's noise"); the minimum is kept. The `U` rows of the two
batches agree to 0.1 G.

### Phase 1: the parts

`S` against `U`, kernel G (3 full runs and 2 without the kernel; `Data` of 997 also 6 and 4), full
G and peak GB, then `hb` of the part and of the checks on twins (`pair_parts.jsonl`):

| part | kernel G `U` | `S` | `S` − `U` | full G `U` | `S` | peak `U` | `S` |
|---|---:|---:|---:|---:|---:|---:|---:|
| weight 4, 37, `Data` | 0.133 | 0.129 | | 17.194 | 17.194 | 0.339 | 0.338 |
| weight 4, 37, `Basis` | 5.615 | 5.902 | +5.1 % | 23.288 | 23.629 | 0.391 | 0.390 |
| weight 4, 37, `Hecke` | 3.623 | 3.963 | +9.4 % | 24.886 | 25.262 | 0.437 | 0.454 |
| weight 4, 37, `QExp` | 0.203 | 0.206 | | 21.194 | 21.199 | 0.389 | 0.389 |
| weight 6, 37, `Data` | 0.136 | 0.131 | | 17.197 | 17.194 | 0.338 | 0.338 |
| weight 6, 37, `Basis` | 18.343 | 19.501 | +6.3 % | 36.236 | 37.439 | 0.581 | 0.597 |
| weight 6, 37, `Hecke` | 8.815 | 9.781 | +11.0 % | 30.878 | 31.874 | 0.692 | 0.730 |
| weight 6, 37, `QExp` | 0.244 | 0.254 | | 21.278 | 21.284 | 0.390 | 0.390 |
| weight 2, 997, `Data` | 3.331 | 3.135 | −5.9 % | 20.481 | 20.284 | 0.406 | 0.404 |
| weight 2, 997, `Data` (6, 4 runs) | 3.335 | 3.133 | −6.1 % | 20.473 | 20.280 | 0.405 | 0.401 |
| weight 2, 997, `Basis` | 6.137 | 6.151 | | 25.442 | 25.449 | 0.428 | 0.427 |
| weight 2, 997, `Hecke` | 23.419 | 23.399 | | 50.981 | 50.965 | 0.735 | 0.733 |
| weight 2, 997, `QExp` | 2.995 | 2.976 | | 27.021 | 27.017 | 0.550 | 0.550 |
| weight 2, 997, `Newforms` | 41.500 | 41.498 | | 77.656 | 77.668 | 0.690 | 0.678 |

| part | `hb` `U` | `S` | the checks on twins, `hb` `U`, `S` |
|---|---:|---:|---|
| weight 4, 37, `Basis` | 8088 | 9068 | `hStarP` 1147, 1292; `hStarM` 1109, 1256; `hDualP` 1131, 1244; `hDualM` 1124, 1234; `hRankR` 901, 1298; `hCuspP` 125, 152; `hCuspM` 121, 147; `hRankB` 42, 57 |
| weight 4, 37, `Hecke` | 4666 | 5338 | `hHecke` 3868, 4540 |
| weight 6, 37, `Basis` | 24857 | 28749 | `hStarP` 5969, 6833; `hStarM` 5393, 6142; `hDualP` 2697, 2996; `hDualM` 2652, 2931; `hRankR` 2173, 3727; `hCuspP` 280, 347; `hCuspM` 275, 340; `hRankB` 42, 57 |
| weight 6, 37, `Hecke` | 11673 | 13440 | `hHecke` 10304, 12071 |
| weight 2, 997, `Data` | 4014 | 3890 | `hWalk` 2113, 1989 |

The parts of 997 other than `Data` hold no check on a twin and are the control: they read the same
to 0.02 G and the same `hb`. `Data` of 37 holds `hWalk` on 38 records, below the meter.

### Phase 1: the decision

Splitting into component walks loses on every check that walks pairs, and so does the variant that
keeps the walks paired. The non-recursive arithmetic of the cusp walk gains 10.1 to 10.2 % on its
check and 6.0 % on its part with no worse peak, which is the rule for that one case,
by a small margin; the gain is 0.20 G of the 76.8 G of level 997, and grows with the number of
generators. Phase 2 builds the pass for that case only, and measures what it does to the rest.

### Phase 2: the pass

`Compute/KernelForm.lean`, about 230 lines: `splitPairs` in the section `Compiler`, `trProj` and
`pushProj` in the translation, four lemmas (`fst_boolRec`, `snd_boolRec`, `fst_intRec`,
`snd_intRec`). After a `kernel_def` `f` is compiled, `splitPairs f` runs; for a definition whose
result or one of whose arguments is `ℕ × ℕ` (`PN` included), with no universe parameter, whose
kernel form holds no recursor of a recursive type with a pair-valued motive (`hasPairWalk`):

- the component forms: `f.fstForm` and `f.sndForm` for a pair result, `f.splitForm` otherwise, on
  the components of the pair arguments (`x_fst`, `x_snd`). Each is compiled by `compile`, the
  compiler of every `kernel_def`, from the projection of the kernel form of `f` on the pair rebuilt
  from its components, so its equation `F.eq_src` is checked by the kernel as for any kernel form;
- a component form is kept only when no pair is left in it, of any type (`hasPairs`); otherwise
  nothing is added for `f` (the environment is put back);
- each comes with a rule, `f.fstForm_eq : Prod.fst (f xs) = f.fstForm xs'`, `f.sndForm_eq`,
  `f.splitForm_eq : f xs = f.splitForm xs'` (`xs'` with every pair argument as its projections),
  proved by `F.eq_src` and unfolding (the pair rebuilt from its projections is the pair, by η).

In the definitions that follow, the translation of `p.fst` on `ℕ × ℕ` (`trProj`) translates `p` and
pushes the projection into it (`pushProj`): the component of a pair `(a, b)`; the projections of
the cases of a `Bool.rec` or an `Int.rec` whose cases are pairs (`fst_boolRec`, …); the component
form of a call, by its rule; the projection otherwise. A call of a definition with a split form is
put on the components by its rule only when one of its pair arguments splits (a pair, cases on
pairs, a call with component forms: `splits`), so that a pair the compiler cannot split (a
variable, the result of a walk) is passed whole and the term does not change.

What it handles: first-order pairs of naturals, results and arguments, through `Bool.rec` and
`Int.rec` (an `if`, a `bif`, a `match` on a sign) and through calls. What it leaves, and why: a
walk with a pair result (`weighFields`, `weighPN`, `weighSlot`, and the definitions around them
whose component forms would only project the walk: `weighPk`, `packPk`, `weighPkPN`, `weighPkSlot`,
`packPN`, `addField`), because its component forms would be component walks (`S`); a pair-valued
function argument (`sc`, `w : ℕ → PN`), because splitting it into two functions applies each at
every use (`R`); a list of pairs (`List PN`, the factorisations `List (ℕ × ℕ)`), which needs the
fusion of the map that builds it with what consumes it; pairs of other types (the entries `ℕ × ℤ`
of a sparse row, the `Int` quadruples of the Heilbronn matrices: `rowModN` gets no component form,
its components project one). `Int` stays.

In the core, 24 component forms: `PN.add`, `PN.sub`, `PN.mul`, `PN.smul`, `PN.ofInt`, `readPN`,
`recPN`, `cuspPN`, `smulSlot` (`fstForm`, `sndForm`); `PN.val`, `PN.beq`, `PN.bias`, `PN.modN`,
`fitsPN`, `det1PN` (`splitForm`). Six kernel forms change: `genCuspOk` (no pair left), `det1PN`
(the projections of its arguments left), `bdSelS` (no pair left), `rowModN`, and the targets
`PN.smul dd (…, …)` of `checkPk` and `rankCheckW`. The readable sources do not change; neither does
a lemma statement, nor the name or the arguments of a definition.

### Phase 2: the cost

`REPEATS=3 SKIP_REPEATS=2 level_cost.py levels docs/bench/kernel_form/pair_level_cost.jsonl TAG
4:37 6:37 2:997 2:23`, tags `before-pair` (the tree at `4c93dce`, built in the worktree) and
`after-pair`:

| part | kernel G before | after | full G before | after | peak GB before | after |
|---|---:|---:|---:|---:|---:|---:|
| weight 4, 37, `Data` | −0.225 | 0.027 | 17.194 | 17.099 | 0.338 | 0.339 |
| weight 4, 37, `Basis` | 5.623 | 5.602 | 23.300 | 23.294 | 0.389 | 0.391 |
| weight 4, 37, `Hecke` | 3.664 | 3.635 | 24.923 | 24.902 | 0.438 | 0.438 |
| weight 4, 37, `QExp` | −0.457 | 0.219 | 21.190 | 21.208 | 0.389 | 0.389 |
| weight 6, 37, `Data` | 0.139 | −0.030 | 17.187 | 17.204 | 0.338 | 0.337 |
| weight 6, 37, `Basis` | 18.734 | 18.379 | 36.640 | 36.281 | 0.585 | 0.528 |
| weight 6, 37, `Hecke` | 8.878 | 8.820 | 30.941 | 30.893 | 0.693 | 0.692 |
| weight 6, 37, `QExp` | 0.243 | 0.248 | 21.280 | 21.288 | 0.391 | 0.391 |
| weight 2, 997, `Data` | 3.352 | 3.154 | 20.484 | 20.307 | 0.407 | 0.403 |
| weight 2, 997, `Basis` | 6.125 | 6.111 | 25.426 | 25.420 | 0.427 | 0.429 |
| weight 2, 997, `Hecke` | 23.427 | 23.372 | 51.011 | 50.968 | 0.733 | 0.734 |
| weight 2, 997, `QExp` | 3.008 | 2.826 | 27.000 | 26.827 | 0.550 | 0.550 |
| weight 2, 997, `Newforms` | 40.120 | 41.457 | 77.682 | 77.633 | 0.649 | 0.713 |
| weight 2, 23, `Data` | 0.085 | 0.084 | 17.125 | 17.146 | 0.337 | 0.336 |
| weight 2, 23, `Basis` | −0.320 | 0.148 | 17.982 | 17.994 | 0.342 | 0.341 |
| weight 2, 23, `Hecke` | −0.886 | 0.489 | 19.400 | 19.413 | 0.352 | 0.352 |
| weight 2, 23, `QExp` | 0.041 | −0.071 | 21.174 | 20.508 | 0.387 | 0.388 |
| weight 2, 23, `Newforms` | 0.836 | 0.452 | 23.576 | 23.209 | 0.411 | 0.410 |

`Data` of 997 is the part the pass changes: its three full runs read 20.682, 20.484, 20.487 before
and 20.503, 20.307, 20.307 after, its runs without the kernel the same (17.13, 17.16). Elsewhere the
differences are the modes of the meter, and `hb` (below) does not move: `Newforms` of 997, whose
checks are untouched, reads its full runs the same to 0.1 G (77.79, 77.68, 79.04 before; 77.74,
77.63, 77.69 after), and its kernel figure moved with the runs without the kernel (37.56, 37.59
before; 36.18, 36.18 after); its peak is the minimum of three runs, 0.649 then 0.716 and 0.722
before, 0.713 to 0.726 after. The peak of `Basis` at weight 6 is the minimum of 0.590, 0.528, 0.528
after and of 0.591, 0.592, 0.585 before, with the same `hb`. The parts of 23 and the small parts of
37 cost less than a gigainstruction and their kernel figures are noise, negative included.

`step4_heartbeats.py run docs/bench/kernel_form/pair_heartbeats.jsonl TAG K:N`, the same tags: of the
checks of the four levels, nine move.

| part | `hb` before | after |
|---|---:|---:|
| weight 4, 37, `Data` | 264 | 260 |
| weight 4, 37, `Basis` | 8088 | 8087 |
| weight 4, 37, `Hecke` | 4666 | 4685 |
| weight 6, 37, `Data` | 264 | 260 |
| weight 6, 37, `Basis` | 24857 | 24855 |
| weight 6, 37, `Hecke` | 11673 | 11709 |
| weight 2, 997, `Data` | 4014 | 3911 |
| weight 2, 997, `Hecke` | 34360 | 34343 |
| weight 2, 23, `Data` | 207 | 205 |

(the parts not listed do not move.) The checks: `hWalk` 2113 to 2010 at 997 (−4.9 %), 96 to 92 at
37, 66 to 64 at 23; `hP2` 2582 to 2565 at 997 (the pair of `rowModN`, through `heckeRowsOn`);
`hRankR` 901 to 900 and 2173 to 2171 (its target `PN.smul d (…, 0)` split); `hHecke` 3868 to 3887
and 10304 to 10340 (+0.5 % and +0.3 %: the target of `checkPk`, split, with the component forms
called where the pair was built once), which the kernel figures of `Hecke` do not see. The hand
split of phase 1 gave `hWalk` 1989 (with the `simp only` of its bridge); the pass gives 2010: its
component forms call one another (`recPN.fstForm` calls `readPN.fstForm`) where the hand-written
ones were flatter.

### Phase 2: the gates

In the worktree, on `v4.37.0-rc1`:

- the core builds without a warning (`lake build`, 9445 jobs); two proofs changed:
  `rankB_of_check` (`Cert/Basis/WeightTwo.lean`), whose `grind` read the kernel form of `bdSelS`
  and now has the rules `PN.smul.fstForm_eq`, `PN.smul.sndForm_eq`; and, in the tests,
  `Step4Eq.bdSelS_eq`, the plain definition rewritten with the same rules before `kernel_rfl%`
  (the projection of an `Int.rec` against an `Int.rec` of projections is equal by cases, not by
  unfolding);
- `check_imports.py` passes;
- the term gates: `compare docs/bench/kernel_form/snapshot_364e70a` exits 0 with one verdict
  changed, `rowModN` (marked `TODO`), from identical up to numerals to different;
  `compare-unmarked docs/bench/kernel_form/snapshot_unmarked` prints what it printed before; a
  snapshot of all the kernel forms taken before the change lists the six above as different and
  every other as identical;
- the tests: `Accepts`, `Audit`, `Shapes`, `Syntax`, `Step4Eq`, `Step5Eq` and the new
  `tests/Pairs.lean` compile with no error, `Faults` and `Rejects` give the errors they list and no
  other; `#kernel_audit strict` passes on 255 kernel forms (231 and the 24 component forms), with
  pairs in 32 instead of 33 (`bdSelS` lost its pair; `genCuspOk` had none in its own term) and
  `Int` in 3 instead of 2 (`PN.val.splitForm`);
- the level targets build without a warning: 37 of weights 4 and 6, 997 and 23 of weight 2
  (9453 jobs).

### What was not done

- The walks and the pair-valued function arguments are not split, by the measurement above. A walk
  that carries both components as two arguments of one recursion, the consumer at its end (the
  "two arguments" of E14), would be neither a pair nor two walks; it was not tried.
- Lists of pairs are not fused with their consumers, and the weight-`w` Heilbronn rows
  (`linMulAux`, `linPow`: lists of pairs in plain definitions) were not measured.
- Phase 1 measured levels 37 and 997; level 23 only in phase 2. The checks of weights 4 and 6 that
  the other agent makes `kernel_def`s at the same time (`killCheck`, `starCheckW`, `checkOnePk`,
  `phiPkOk`, …) were plain definitions here; after the merge the rules apply to them as to every
  `kernel_def`, which was not measured.
- `lake build Levels` and `lake exe axioms` were not run (only the four level targets); every
  generated equation is checked by the kernel, with no `sorry`.

### To run it again

From the repository root, each line under the machine's lock, `KERNEL_FORM_WORK` set and
`A=scripts/bench/kernel_form/pair_ab.py`. Phase 1 compares with the tree before the pass (`4c93dce`):
the files of `PairSplit/` compile after it too, but there the pair forms `U` already have the cusp
walk split.

```
python3 $A lib
python3 $A checks OUT.jsonl 4:37 Basis hDualP copies=8           # and twin=R; the table above
python3 $A checks OUT.jsonl 2:997 Data hWalk copies=5
python3 $A prepare 4:37 6:37 2:997
python3 $A build 4:37 6:37 2:997
python3 $A heartbeats OUT.jsonl 4:37 6:37 2:997
python3 $A measure OUT.jsonl 3 2 4:37 6:37 2:997
python3 $A measure OUT.jsonl 6 4 2:997/Data
python3 $A report OUT.jsonl
```

Phase 2, before and after, in a tree at commit `4c93dce` with `pair_pass.patch` applied:

```
REPEATS=3 SKIP_REPEATS=2 python3 scripts/bench/kernel_form/level_cost.py levels docs/bench/kernel_form/pair_level_cost.jsonl TAG 4:37 6:37 2:997 2:23
python3 scripts/bench/kernel_form/step4_heartbeats.py run docs/bench/kernel_form/pair_heartbeats.jsonl TAG 4:37    # and 6:37, 2:997, 2:23
python3 scripts/bench/kernel_form/level_cost.py report docs/bench/kernel_form/pair_level_cost.jsonl before-pair after-pair
python3 scripts/bench/kernel_form/step4_heartbeats.py report docs/bench/kernel_form/pair_heartbeats.jsonl before-pair after-pair
lake env lean -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false scripts/bench/kernel_form/tests/Pairs.lean
```
