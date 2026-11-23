# Measuring the compiler

What a change to the compiler is measured with, and how. The tools are `scripts/kernel_cost.py`
(instructions, time and memory of a file), `scripts/heartbeats.py` (allocations of each
declaration), `scripts/term_gate.py` (the terms the compiler produces) and `#kernel_audit` (what
a kernel form still contains). The methods come from the experiment in ModularSymbolsTau
(`docs/history/kernel_form_README.md`, "Method"; `docs/history/E14.md`; `docs/techniques/`).

## What there is to measure

- The checks. The cost of deciding a check `f xs = true` by `decide +kernel`, through the kernel
  form `f` and through the readable definition `Src.f` (what the compiler buys), or through the
  kernel forms of two versions of the compiler (what a change buys). The files of `bench/` hold
  such checks on synthetic data.
- The compiler. The cost of elaborating a `kernel_def`: the readable definition, the translation,
  the equation, the kernel's check of the equation, the generated equations. Here it is paid by
  the tests and by the files of `bench/`, which compile their own `kernel_def`s; at scale, by a
  client's own `kernel_def`s.
- The output. The term of every kernel form of the library forms and the tests against a baseline
  (the term gate), and what each still contains (the audit).

Correctness is not measured: the kernel checks every `f.eq_src` at every build, so a kernel form
that exists is equal to its readable definition. What can go wrong unseen is cost: a term that is
equal but slower, or a source that compiles to a different check.

## The instruction meter

`scripts/kernel_cost.py` runs `lean` on a file under `/usr/bin/time -l` and reads three figures
from it: instructions retired (the measure), peak memory footprint, and wall time. The runs go
through `scripts/meter.py`, shared with `heartbeats.py` and the technique benchmarks.

```
python3 scripts/kernel_cost.py run OUT.jsonl TAG FILE.lean [FILE.lean ...]
python3 scripts/kernel_cost.py report OUT.jsonl TAG_A TAG_B
python3 scripts/kernel_cost.py noise FILE.lean [RUNS]
```

- Every file runs in full and with `-Ddebug.skipKernelTC=true`. The option makes `addDecl` add
  each declaration without the kernel's check; parsing, elaboration and compilation are the
  same. The full run gives `G`, the skip run `skip_G`, and the kernel's work
  is `kernel_G = G − skip_G`. A `decide +kernel` check is evaluated by the kernel only, so all of
  its evaluation is in `kernel_G`; so is the kernel's check of every `f.eq_src`. A proof by
  `rfl` or `decide` (without `+kernel`) also makes the elaborator evaluate: that part is in
  `skip_G`.
- Kernel time is the wall time of the full run less that of the skip run. The peak is that of
  the full run.
- Every file runs `REPEATS` times in full (3 by default) and `SKIP_REPEATS` times without the
  kernel (by default as many), and the minimum of each is kept: what disturbs a run only adds to
  it. The figures of every run are kept in the row beside the minima: look at them before
  trusting a minimum.
- `lean` runs single-threaded, `-j1 -DElab.async=false`, with the options of `lakefile.toml`
  but its linters: `-DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true`
  (the last so that the messages a `#guard_msgs` expects print as in a build). The options are
  `OPTS` of `scripts/meter.py`. The instruction count covers every thread of the process, but
  with asynchronous elaboration the kernel's checks run in tasks beside the elaborator, and the
  peak and the wall time then depend on scheduling. Without the linters the full figures are below those of a
  `lake build` of the same file; the kernel figures are the same.
- `lean` is the toolchain's binary with the project's search path (found once through `lake env`),
  run directly, never through `lake`: on macOS the counters of `/usr/bin/time -l` are those of the
  process it starts, so a run through `lake env lean` would count the wrapper only.
- A file runs in place and imports built modules: `lake build` first, and after every change of
  the compiler.
- Every run is capped, `MEM_LIMIT_GB` (24 by default) and `TIME_LIMIT_S` (1800 s); a run past a cap
  is killed and recorded as such.
- One row a file and tag, a JSON line: `G` and `G_all` (the minimum and every full run), `skip_G`,
  `kernel_G`; `real_s`, `skip_real_s`, `kernel_s`, the same in wall seconds; `peak_GB` and
  `peak_all`; `tag`, `file`, `repeats`, `commit`, `compiler` (the hash of
  `KernelDef/KernelForm.lean`) and `opts`. `report` prints the two tags side by side, one line a
  file.

The noise. The runs of one file differ by up to 1 G and more: in ModularSymbolsTau, a file of
about 25 G read 24.41 to 26.08 G over ten runs, and one file's runs fell in two groups 1.5 G
apart. `kernel_G` is the difference of two minima, each good to a few tenths of a G on files of
20 to 30 G, so a kernel figure carries the noise of two runs; `G` is the steadier figure. The peaks
of the runs of one file agree to about 0.008 GB. `noise FILE [RUNS]` runs a file `RUNS` times (10
by default) in full and prints the spread of `G`: run it on a file before reading a difference on
it.

Two traps, both met in ModularSymbolsTau:

- A check of 1 G cannot be compared in one copy. State it `k` times in its file, so that the
  kernel's work is multiplied and the rest of the file is not.
- A copy with the same statement is not checked again: `decide +kernel` proves a statement through
  an auxiliary lemma it finds again by the statement, so forty copies of a theorem cost one. Copy
  `i` states `Nat.beq i i = true ∧ …`. Likewise, a variant that replaces the heads of a bundle of
  conjuncts can lose a computation the conjuncts shared by naming the same term: a variant
  rebuilds the whole statement.

Wall time is not the measure: it stalls intermittently on this machine (a run once took 48 s at
unchanged instructions), and a build that stalls with low CPU is the machine (a file scan), not
the code. Instructions and peak memory are the measure; times are reported beside them.

The peak moves with things that change no term. In ModularSymbolsTau one file's peak rose by
0.02 GB when the compiler's module was added to its imports, with every term the same: it is a
matter of how the memory freed by one declaration is reused by the next. A peak difference of a
few hundredths of a GB on one file is not a finding until it is reproduced on others.

The data of a bench file. A big literal written as text is elaborated slowly (the reading of
numerals is quadratic in their length), and `OfNat` numerals in a `def` cost 2.7 times the
elaboration of raw literals in a `noncomputable def` (`docs/techniques/natlit/`). The files of
`bench/` hold their data as raw literals in `noncomputable def`s (`abbrev z : ℕ := nat_lit 0` for
the elements of `Length`), of a size at which the kernel's work is visible over the file; the two
files of a check hold the same data, so its elaboration is the same in each. The data is not free
for the kernel either: it checks the definitions that hold it, and the `kernel_def`s of the file
with their equations, the same in both files, so the difference of the two is the checks'.

The meter reads macOS's `/usr/bin/time -l`. All figures here are from one machine, an Apple M5
with 32 GB; they compare across tags, not across machines.

## Heartbeats

`scripts/heartbeats.py` copies each file (by default every file of `KernelDefTest/` and
`bench/`) into `KERNEL_DEF_WORK/hb/TAG/` (`kernel_def_work` in the system's temporary folder by
default), with `#count_heartbeats in` (`Mathlib.Util.CountHeartbeats`) before every `kernel_def`
and every declaration that holds `decide +kernel` (a theorem, a lemma, an `example`), runs the
copy once with the options of the meter, and writes one row a declaration: `file`, `name` (an
`example` is `example#k`, the `k`-th of its file), `kind` (`kernel_def` or `decide`), `line`,
`hb`, with `tag`, `commit` and `compiler`. A file that fails gives one row with `error`.

```
python3 scripts/heartbeats.py run OUT.jsonl TAG [FILE.lean ...]
python3 scripts/heartbeats.py report OUT.jsonl TAG_A TAG_B
```

- A heartbeat is a small allocation of the Lean process, counted in thousands (the unit of
  `maxHeartbeats`). It counts the allocations of the elaborator and of the kernel: with
  `Elab.async` off, the kernel checks a declaration inside its command, so its work is in the
  count.
- The count is deterministic: the same at every run, whatever the load of the machine. A
  difference of one is real, and "nothing moved" can be said to the unit, which the instruction
  meter cannot.
- On a `kernel_def`, it is the compiler's own cost for that definition: the readable definition,
  the translation, the equation and its kernel check, the generated equations. A plain `def` of
  the same body pays the first part only: the difference of the two is the compiler's overhead.
- On a `decide +kernel` theorem, it is the cost of the check, almost all of it the kernel's
  evaluation. It follows the kernel's instructions: in ModularSymbolsTau, plain definitions
  against kernel forms gave a ratio of 3.23 in heartbeats and 3.10 in kernel instructions on the
  same file.
- It counts allocations, not instructions: a step that is one operation on big numbers allocates
  little whatever their size, and the import of a file is not in any row. Heartbeats say where a
  cost is and whether it moved; the meter says how much it is.
- `report` prints the totals of the two tags by kind and by file, then every declaration whose
  count moved, largest change first (`TOP` rows, all when `TOP` is unset).

The compiler is paid in two places: in each `kernel_def` (its heartbeats) and in the import of
the compiler itself. `KernelDef/KernelForm.lean` imports five modules of Lean, not `import Lean`:
in ModularSymbolsTau, a file with the two imports of its first kernel-evaluated module cost
10.95 G alone, 13.32 G with a compiler that imported `Lean`, and 11.00 G with the five modules. A
wider import is paid by every file of every client.

`trace.profiler` with `-DElab.async=false` gives the time of each declaration too, but times are
noisy and only the synchronous ones mean anything (`docs/history/E14.md`, the caveats).

## The term gate

`scripts/term_gate.py` compares the term of every kernel form with a snapshot.
`test/golden/` is the baseline: the terms of 127 definitions (the 42 library forms of
`KernelDef/` and the 85 definitions the tests accept), which every compiler change is compared
against. It does not read `bench/`: the kernel forms of a bench file are compiled anew at every
run, so a compiler change shows there in the cost, not in the gate.

```
python3 scripts/term_gate.py list
python3 scripts/term_gate.py snapshot DIR
python3 scripts/term_gate.py compare DIR [FILE.lean ...] [--map OLD=NEW ...]
```

- `list`: the `kernel_def`s of `KernelDef/` and `KernelDefTest/` (file, line, full name), read
  off the sources. Those a test expects the compiler to reject (a `kernel_def` under
  `#guard_msgs` whose expected message is an `error:`) are listed apart and left out of
  `snapshot` and `compare`.
- `snapshot DIR`: for each, the type and the value of the constant of the present build in a
  canonical form: constants by name, universe levels (the parameters of the definition
  numbered), literals, de Bruijn indices; no binder name, no binder annotation, no metadata. One
  JSON file a definition, with three more forms of the value: η-reduced, with the `OfNat`
  numerals of `ℕ` as raw literals, and both; and `DIR/INDEX.json`, the list.
- `compare DIR`: the same for the present build, for every `kernel_def` of the sources (of the
  files given, when files are given), against the definition of the same name in the snapshot.
  `--map OLD=NEW` (repeatable) compares under a renaming: a constant `OLD` (or `OLD.x`) of the
  snapshot is read as `NEW` (`NEW.x`), in the names of the definitions and inside the terms. The
  port from ModularSymbolsTau was accepted so, with its snapshot and the names that moved into
  `KernelDef` (`ModularSymbolsTau.Compute.Pack.listGetD=KernelDef.listGetD`, …).
- `lean` runs once, through `lake env lean` from the repository root, on a generated file that
  imports the modules of the definitions: `lake build` first.

The verdicts, one line a definition:

- `identical`;
- `identical up to η`, of the outer `fun` and wherever `Expr.eta` reduces: the kernel's work is
  the same;
- `identical up to numerals`, an `OfNat` numeral against a raw literal, possibly with η: the raw
  literal is the form the playbook asks for, and the difference costs under 1 % a use;
- `DIFFERENT`, with the first place where the two values part;
- `TYPE CHANGED`, when the type is not that of the snapshot (an argument moved);
- `NEW`, a definition that is not in the snapshot;
- `MISSING`, a definition of the snapshot that is not among the sources (checked only when no file
  is given).

The exit code is 1 when a definition is not identical up to η (up to numerals for an entry whose
`todo` is true in the index), has a changed type, is new or is missing.

When a difference is expected:

- After a change that should not change the output (a refactoring of the compiler, a feature for
  a construct no test uses, a bump of the toolchain), none: every line is `identical`.
  After the bump to `v4.37.0-rc1` every verdict in ModularSymbolsTau was the same.
- After a change meant to change the output (a new translation, a new `@[kernel_rule]`), the
  `DIFFERENT` lines are exactly the definitions that use what changed, and the first difference of
  each is the intended one. A definition that differs and should not is the finding.
- After a new test, its `kernel_def`s as `NEW`; after a test is removed, its definitions as
  `MISSING`.
- `TYPE CHANGED` is never expected from a compiler change: the kernel form has the type of the
  readable definition. It means that a source changed.

Why it matters though `f.eq_src` is checked: the equation proves the kernel form equal to its
source, not the source equal to what was meant. A precedence slip in a source (`a / b <<< c` is
`a / (b <<< c)`) is a different check that still compiles, with its own equation; only the
comparison with the term it replaces finds it. And an equal term can cost more: a construct the
compiler stops recognising stays in the term (an `ite`, a matcher), which the gate shows as a
difference and the audit as a miss.

A difference is accepted by taking a new baseline, `term_gate.py snapshot test/golden`, and only
after the other gates and the measurements (`CLAUDE.md`, "The gates of a compiler change").

## The audit

`#kernel_audit [strict] [f g …]` (`docs/KERNEL_DEF.md`, "The audit") reads the kernel forms named,
or all of the environment, and sorts what they still contain into two groups:

- the misses of the compiler: `ite`, `dite`, a matcher (`casesOn` included), `brecOn`,
  `WellFounded.fix`, `let`, `Decidable.decide`, an operation through an instance at a type other
  than `ℤ`, a call of a list function of the core or of another library function (`Nat.log2`
  included, which is no primitive of the kernel), a call of a readable definition `Src.g` or of an
  auxiliary one;
- the representation it keeps by design: pairs, `Int`, and the fields of a structure (`.proj`,
  and the projection functions of a structure that is not a class, such as `Array.toList`).

`KernelDefTest/Audit.lean` imports every other test module and runs `#kernel_audit` over every
kernel form of the environment (the library forms and the tests). Not `strict`, since two tests
make misses on purpose (`Rejects.getOr`, `Syn.total`) and the two library forms generic in a type
class keep its instance (`listElem`, `listSum`): the line of misses of its report is pinned by
`#guard_msgs (substring := true)` to those, so any new miss changes it and fails `lake build`.
While writing a definition, `#kernel_audit f` shows its own.

A miss means the compiler did not recognise a construct: rewrite the source, or teach the compiler
(a translation, or a kernel form and a `@[kernel_rule]` in a module of `KernelDef/`). The audit
reads a kernel form, not the definitions it calls: a call of a plain `def` of the user's code is
not a miss, and that `def` is not audited. The user's code is the modules whose root holds a
kernel form, and the module being checked (`userRoots`); a call into any other root is a library
call. The audit says what is left; the term gate says what changed.

## What each construct costs

The criterion a kernel form is held to applies to the term, what `#print f` shows, not to the
source (`docs/history/E14.md`):

- its loops are bare recursors, not structural recursion (`brecOn`) or well-founded recursion;
- no `let`, tuple or structure projection, nothing from `Int`, `Fin` or Mathlib (the compiler
  keeps pairs and `Int`: they are the representation the author chose);
- inside a loop body, or in anything called from one: no instance arithmetic, `ite`, `&&`,
  matcher; an `OfNat` numeral is allowed;
- what it calls is itself in this form. What runs once per check (a top-level `&&`) is allowed.

Per use inside a `Nat.rec` loop whose step costs 31 to 37 k instructions:

| construct, against the fast form | extra instructions per use |
|---|---:|
| `OfNat` numeral `3`, against `nat_lit 3` | +0.1–0.25 k (under 1 %) |
| `Nat.blt` against `Nat.ble` as the test of a `Bool.rec` | +9 k |
| `&&` against nested `Bool.rec` | +8.5 k |
| `let` | +7.8 k |
| tuple and projection (`(Prod.mk a b).1`) | +12.9 k |
| `r + 3` (`HAdd.hAdd`) against `Nat.add r 3` | +19 k (+60 %) |
| `if r ≥ 7` (`ite`, `Nat.decLe`) against `Bool.rec` on `Nat.ble` | +64 k (4.8 times the raw test) |
| structural recursion against a bare recursor | 2.7 times per element |

`docs/techniques/` measures each technique alone, on synthetic files that import nothing, with
`scripts/techniques/run_<t>_bench.py`; its README says which of them the compiler applies. Those
files run with `lean`'s defaults, not with the options of the meter, as in ModularSymbolsTau, and
their plots need matplotlib (`sage -python … plot`).

## Baseline (2026-11-22)

The first measurement of the repository, on the files of `bench/`: Apple M5, 32 GB, Lean
`v4.37.0-rc1`, `REPEATS=3`. Kernel G, the minimum of three runs, through the kernel form and
through `Src.f`:

| check | kernel form | `Src.f` | ratio |
|---|---:|---:|---:|
| `Shape` | 1.151 | 3.506 | 3.0 |
| `HalvingRead` | 2.577 | 8.765 | 3.4 |
| `RowProduct` | 1.917 | 3.844 | 2.0 |
| `Length` | 1.040 | 3.794 | 3.6 |

- Each bench file compiles its own `kernel_def`s, so the kernel also checks those definitions and
  their equations within the run, the same in both files of a pair. That is why `RowProduct`
  costs 1.92 G here against 1.79 G when its definitions were imported from built modules. The
  decided terms are the same, but for their names.
- Single runs spread up to 0.42 G, and the first run of a file is cold; the minimum of three is
  stable to about 0.02 G.
- Heartbeats of the `2^14` check of `Length`: 1199 through `listLength`, 4390 through
  `List.length` (3.66 times). Heartbeats are identical from run to run.

The rows are in `docs/baseline/`: `kcost.jsonl` (`kernel_cost.py`, tag `base`, the eight files of
`bench/`) and `hb.jsonl` (`heartbeats.py`, tag `base`, 115 rows from `KernelDefTest/` and
`bench/`).

The bench pairs of the library forms (`Log2`, `Sqrt`, `ListMax`, `ArrayFoldl`, `ForallLt`,
`Prime`, `Count`, `Sum`, `Reverse`, `IntLt`, `IntAdd`, `TestBit`, `Fib`) were measured the same
way when they were added, tag `libforms` in the same two files (26 rows of `kcost.jsonl`, 104 of
`hb.jsonl`); their table and the import cost of the root before and after are in
`docs/library_forms/README.md`.

## Comparing two versions of the compiler

Tag A is the compiler before the change, tag B after it; both are measured on the same files,
close in time, with nothing heavy running beside.

1. Before the first edit, build (`lake build`) and measure tag A:
   `kernel_cost.py run OUT.jsonl A FILES` and `heartbeats.py run OUT.jsonl A FILES`. If the change
   is already made, measure A in a worktree at the base commit (built there), or stash the change,
   build, measure and restore.
2. Make the change, then pass the gates (`CLAUDE.md`): `lake build`, the audit,
   `term_gate.py compare test/golden`, every difference reviewed.
3. Measure tag B on the same files, with the same `REPEATS` and `SKIP_REPEATS`.
4. `kernel_cost.py report OUT.jsonl A B` and `heartbeats.py report OUT.jsonl A B`. When a result
   is near the noise, run A again after B: the machine may have changed state.

Which files:

- Identical terms cost the same (in ModularSymbolsTau, −0.4 to +0.5 %, inside the noise). The
  term gate says whether the terms of the library forms and the tests changed; it does not read
  `bench/`, whose kernel forms are compiled at every run, so run the bench pairs whenever the
  change could touch a construct they use. When no term changed, measure only the compiler's
  cost: heartbeats of the test and bench files, and the meter on a file that imports the compiler
  and nothing else.
- If terms changed, measure the checks too: the bench pairs that use what changed, and a new pair
  when none does. The `Src` files are the reference: their readable
  definitions do not change with the compiler (down to calls of kernel forms of another
  namespace, which do).
- A change to `KernelDef/ListForms.lean` changes the definitions that call the list function: the
  term gate names them.

The files of `bench/`. Each check is two files: `bench/<Check>.lean` decides it through the
kernel form, `bench/<Check>Src.lean` through the readable definition `Src.f`, so that
`kernel_cost.py` meters the two paths apart and a change of the compiler shows in the first. Each
file states the check at three sizes, one theorem a size, on data drawn from a seeded generator.
Each file is self-contained: it imports `KernelDef` only and defines the readable `kernel_def`s of
its check, copied from ModularSymbolsTau's `Compute/` with their namespaces mirrored under
`KernelDefBench.<Check>`, so that their terms are those of the client but for the names. The pairs
are `Shape` (`shapePk`, a walk of packed sparse rows), `HalvingRead` (`sumRd`, every slot
of a packed natural read through `rdH`), `RowProduct` (`e2RowsCheck`, a product checked row by
row) and `Length` (`l.length`, `listLength` against core's `List.length`). They are generated, by
`python3 scripts/gen_bench.py [OUT_DIR]` (into `bench/` by default): change the generator and
regenerate, never edit the files by hand. A new check is a new generator in `gen_bench.py`, added
to the list its `main` writes. `scripts/run_tests.sh` checks that every file elaborates.

Write the measurement up in `docs/`, a folder per measurement: its rows (`*.jsonl`) and a README
with the question, the answer, the method (machine, toolchain, commits, `REPEATS`), the tables,
what was not done, and the commands to run it again. `docs/history/kernel_form_README.md` is the
model.
