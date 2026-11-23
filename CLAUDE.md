# Kernel_def — the `kernel_def` compiler, on its own

## Goal

Develop, test, measure and grow the `kernel_def` compiler: a Lean 4 command that takes a
definition written in ordinary notation and produces the term Lean's kernel evaluates fast (bare
recursors, `Nat.*` heads, raw literals, `Bool.rec` on `Nat.ble`), with an equation the kernel
checks.

- What it does, with examples: `docs/KERNEL_DEF.md`.
- How it is measured: `docs/MEASURING.md`.
- What each construct costs the kernel, measured alone: `docs/techniques/`.
- How it was built and measured in ModularSymbolsTau: `docs/history/`.

## Relation to ModularSymbolsTau

- The compiler originated in ModularSymbolsTau (`/Users/nicolafalciola/ModularSymbolsTau`), a
  certified computation of modular forms whose checks are decided by `decide +kernel`, and was
  moved here; `docs/history/` is the record of how it was built and measured there.
- The two projects are independent. Never import ModularSymbolsTau, and never copy code from it,
  except the definitions that `scripts/gen_bench.py` writes into `bench/`, namespaced, to have
  real checks to measure.
- No change here is ported back, and none is required to pass ModularSymbolsTau's gates: the gates
  of a change are this repository's (below).

## Trust model (invariant)

- The compiler is untrusted. `f.eq_src : f xs = Src.f xs` is added with `addDecl`, so the kernel
  checks it; the axioms of every generated theorem are collected; when the readable definition
  has an error, the compiler fails or the kernel rejects the equation, nothing is added. A wrong
  compiler can only fail to compile, or compile to an equal term that costs more: the term gate
  and the audit are for the second.
- No `sorry`, no `native_decide`. Axioms ⊆ {`propext`, `Classical.choice`, `Quot.sound`}:
  `KernelDefTest/Axioms.lean` checks every kernel form, the theorems generated for it and every
  declaration of `KernelDef/` and `KernelDefTest/`, and fails the build otherwise;
  `scripts/run_tests.sh` checks the sources for `sorry`, `admit` and `native_decide`.

## What the compiler does and does not do

- It changes notation and control flow, not representation. Arithmetic and tests on `ℕ` become
  the kernel's primitives, numerals raw literals, `if`, `&&`, `match` and `let` become `Bool.rec`,
  recursors and substitution, `List.all` and the like a `List.rec`, structural recursion a bare
  recursor. Pairs, projections and `Int` stay: a definition on them carries
  `-- TODO: kernel form: …`. Literal constants, walking instead of indexing, halving reads stay
  the author's choices.
- Rejected: well-founded recursion, mutual and nested recursion, and a recursive call that is not
  on a field of the constructor matched (or on a constructor rebuilt from the fields of a case on
  such a field).
- Kept, and reported by `#kernel_audit` as a miss: a `dite` whose proof is used, a `where`
  helper, a library function with no kernel form in the modules of `KernelDef/`.
- It leans on internals of the toolchain: the shape of `ite` and `Decidable`, matchers, the
  equation names Lean reserves, `markAsRecursive`, `csimp`. Rerun the gates after a bump.

## Layout

| path | content | may import |
|---|---|---|
| `KernelDef/KernelForm.lean` | the compiler, namespace `KernelDef`: sections `Rules`, `Registry`, `Translation`, `Compiler`, `Audit`, `Commands` | the five modules of Lean it imports now |
| `KernelDef/ListForms.lean` | 28 kernel forms and 40 `@[kernel_rule]`s of functions of the core on lists, arrays and `Option` (`List.length`, `List.getD`, `List.foldl`, `List.sum`, `l[i]?`, `List.elem`, `List.max?`, `Array.foldl`, `Option.getD`, …) and of `Nat.choose` | `KernelDef.KernelForm`, Mathlib |
| `KernelDef/NatForms.lean` | 7 kernel forms and 9 rules on `ℕ`: `Nat.log2` (no kernel primitive), `Nat.sqrt`, `Nat.testBit`, `min`, `max`, `Nat.pred`, `Nat.lcm`, `Nat.all`, `decide (∀ i < n, p i)` | `KernelDef.KernelForm`, `Mathlib.Data.Nat.Notation` |
| `KernelDef/IntForms.lean` | 11 rules on `ℤ` (the core's kernel forms `Int.add_k`, …, `Int.blt'`) and the kernel form `intBEq` | `KernelDef.KernelForm`, `Mathlib.Data.Int.Notation` |
| `KernelDef/MathlibForms.lean` | optional (not imported by the root): 6 kernel forms and 4 rules for Mathlib's `decide (Nat.Prime p)`, `Nat.fib`, `Nat.factorial`, `Nat.digits` | `KernelDef`, four modules of Mathlib |
| `KernelDef.lean` | the root: a client imports it; it imports every module of `KernelDef/` but `MathlibForms` | `KernelDef` |
| `KernelDefTest/` (lean_lib, globbed) | 12 files: `Accepts`, `Rejects`, `Faults`, `Shapes`, `Syntax`, `LibraryForms`, `NatForms`, `IntForms`, `MathlibForms`, `DocExamples` (the worked examples of `docs/KERNEL_DEF.md`, their outputs pinned), `Audit` (`#kernel_audit` over every kernel form, its misses pinned), `Axioms`: 85 `kernel_def`s accepted, 4 rejected by design | `KernelDef`, Mathlib, `KernelDefTest` |
| `bench/` | pairs of files, `<Check>.lean` and `<Check>Src.lean`, that decide a check through its `kernel_def` and through its `Src.f` on synthetic data, for `kernel_cost.py`: `Shape`, `HalvingRead`, `RowProduct`, `Length`, and the library forms `Log2`, `Sqrt`, `ListMax`, `ArrayFoldl`, `ForallLt`, `Prime`, `Count`, `Sum`, `Reverse`, `IntLt`, `IntAdd`, `TestBit`, `Fib`. Self-contained: each file defines the readable `kernel_def`s of its check (the first four copied from ModularSymbolsTau's `Compute/`), namespaced (`KernelDefBench.<Check>`). Generated by `scripts/gen_bench.py`, never edited by hand; not a library | `KernelDef` (and `KernelDef.MathlibForms`) only |
| `test/golden/` | the term-gate snapshot of the 127 kernel forms (42 library forms, 85 test definitions): the baseline of compiler changes | |
| `scripts/` | the tools (Python 3): `run_tests.sh`, `term_gate.py`, `kernel_cost.py`, `heartbeats.py`, `meter.py` (the meter they share), `gen_bench.py`; `scripts/techniques/`, the technique benchmarks; `scripts/library_forms/`, the benchmark of the library forms (`libbench.py`, `analyze.py`, `Export.lean`) | |
| `docs/` | the documentation, the measurements and their write-ups | |

- The surface names are fixed: `kernel_def`, `@[kernel_inline]`, `@[kernel_rule]`,
  `#kernel_audit [strict]`, `Src.f`, `f.eq_src`, `f.src_eq`, `f.eq_src_fun`. Clients
  use them.
- `KernelDef/KernelForm.lean` imports five modules of Lean, not `import Lean`: every file of every
  client pays for its imports (about 2.4 G of instructions for `import Lean`,
  `docs/MEASURING.md`). Widen them only with a measurement.
- New code goes in the namespace `KernelDef`; each test file in `KernelDefTest.<Name>`; each bench
  file in `KernelDefBench.<Check>`.
- `KernelDefTest` is globbed: every file in it is built. No scratch files there, nor in `bench/`,
  whose files are regenerated, never edited by hand.

## Building

- Always run `lake` from the repository root `/Users/nicolafalciola/Kernel_def`.
- Toolchain `leanprover/lean4:v4.37.0-rc1`, Mathlib at `v4.37.0-rc1` (`lakefile.toml`). Bump
  only deliberately, with `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` together,
  and rerun every gate: the compiler leans on internals of the toolchain, and the kernel's
  primitives can change (in `v4.37.0-rc1`, `Nat.log2` is not one).
- First build: Mathlib's oleans come from `lake exe cache get`.
- A build or a run that stalls with low CPU is the machine (a file scan can hold an import for
  minutes), not the code: compare CPU and elapsed time before blaming a change.
- Commands:
  - `lake build`: `KernelDef` (globbed, so `MathlibForms` too) and `KernelDefTest`: the compiler,
    the library forms and the tests, every `f.eq_src` checked by the kernel, the audit and the
    axiom check included.
  - `lake build KernelDefTest.Audit`: one module, here the audit.
  - `scripts/run_tests.sh`: the test suite, five gates, about 110 s (gate 5, the bench files, about
    80 of them); it exits non-zero when one fails and names it. `NO_BENCH=1` skips gate 5.
    1. `lake build` (`KernelDef`, `KernelDefTest`): no error, no warning.
    2. `term_gate.py compare test/golden`: the 127 kernel forms identical to the snapshot.
    3. Import coverage: `KernelDefTest/Axioms.lean` imports every module of `KernelDefTest/`, and
       `Audit.lean` every one but `Axioms.lean`.
    4. No `sorry`, `admit` or `native_decide` in the 52 Lean files, comments left out.
    5. The 34 files of `bench/` elaborate with no error (each in a few seconds).
  - `python3 scripts/term_gate.py {list | snapshot DIR | compare DIR [FILE.lean …] [--map OLD=NEW …]}`:
    the `kernel_def`s of `KernelDef/` and `KernelDefTest/`, a snapshot of their terms, the
    comparison with one. It does not read `bench/`.
  - `python3 scripts/kernel_cost.py {run OUT.jsonl TAG FILE.lean … | report OUT.jsonl TAG_A TAG_B |
    noise FILE.lean [RUNS]}`: instructions, time and peak of a file, in full and without the
    kernel (`REPEATS`, `SKIP_REPEATS`; caps `MEM_LIMIT_GB`, `TIME_LIMIT_S`).
  - `python3 scripts/heartbeats.py {run OUT.jsonl TAG [FILE.lean …] | report OUT.jsonl TAG_A TAG_B}`:
    the heartbeats of every `kernel_def` and every `decide +kernel` declaration (by default of
    `KernelDefTest/` and `bench/`).
  - The two meters run `lean` through `scripts/meter.py`, with `-j1 -DElab.async=false
    -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true`.
  - `python3 scripts/gen_bench.py [OUT_DIR]`: writes the files of `bench/`.
  - `python3 scripts/techniques/run_<t>_bench.py run [OUT.jsonl]`, then
    `sage -python scripts/techniques/run_<t>_bench.py plot OUT.jsonl` (the plot needs
    matplotlib), for `t` in `natlit`, `length`, `branch`, `let`, `index`, `slotread`; `OUT`
    defaults to `docs/techniques/<t>/results.jsonl`.
  - `python3 scripts/library_forms/libbench.py {export | run [OUT.jsonl] [CANDIDATE|GROUP …] |
    list | src C V N}`, then `python3 scripts/library_forms/analyze.py [OUT.jsonl]`: library
    functions against their kernel forms on files that import nothing
    (`docs/library_forms/README.md`; about 90 minutes for the whole sweep).
- Filtering build output: `2>&1 | /usr/bin/grep -E "error:|warning:|Build completed"`.

## The gates of a compiler change

In this order (`docs/MEASURING.md` explains each). `scripts/run_tests.sh` runs the first three,
with the checks of imports, of `sorry` and of the bench files.

1. `lake build`: every `eq_src` checked, every test passes, no warning.
2. The audit (`KernelDefTest/Audit.lean`, part of `lake build`): `#kernel_audit` over every kernel
   form, its line of misses pinned by `#guard_msgs (substring := true)` to those that tests make
   on purpose (`Rejects.getOr`, `Syn.total`) and the instances of the two library forms generic in
   a type class (`listElem`, `listSum`). Any new miss fails the build.
3. `python3 scripts/term_gate.py compare test/golden`: every difference reviewed. A difference
   must be one the change intends, in the definitions it targets. A precedence slip in a source
   compiles, with its equation, and is a different check: only this comparison finds it.
4. Then measure: `kernel_cost.py` and `heartbeats.py`, tag A before the change and tag B after,
   on the files of `bench/` (each compiles its own `kernel_def`s, so it shows the change both in
   its checks and in the compiler's own cost) and on the tests. Write the result up in `docs/`.
5. Only then `python3 scripts/term_gate.py snapshot test/golden`, to accept the new baseline, in
   the same commit as the change.

## How to add a test, a library form or a bench check

- Accepted: a `kernel_def` and an `example … := by decide +kernel` on it in
  `KernelDefTest/Accepts.lean` (a construct the compiler now takes) or `Shapes.lean` (a shape of
  recursion or matching); `Syntax.lean` for modifiers and surroundings (`private`, universes,
  section variables, `where`). Where the term matters, pin it with `#guard_msgs in #print f`.
- Rejected: in `KernelDefTest/Rejects.lean`, the `kernel_def` under `#guard_msgs in`, the
  expected error in the docstring of `#guard_msgs`, then `#check_failure f` under `#guard_msgs`
  (expecting `Unknown identifier`): the error is the one expected, and nothing was added. The term
  gate leaves such a definition out.
- Fault: `KernelDefTest/Faults.lean`, for what happens around an error (an error of the readable
  definition adds nothing, an attribute goes to the kernel form, numerals become raw literals).
- Audit: a definition with a miss goes in the namespace `KernelDefTest.AuditFaults` of
  `KernelDefTest/Audit.lean`, with its `#kernel_audit` report under `#guard_msgs`, after the audit
  of everything. A test elsewhere that makes a miss on purpose changes the pinned line of misses
  at the top of `Audit.lean`: update it, saying why in the docstring. A new test module is
  imported by `Audit.lean` and `Axioms.lean` (gate 3 checks it).
- An example of `docs/KERNEL_DEF.md`: written, or changed, in `KernelDefTest/DocExamples.lean`
  first, its outputs pinned by `#guard_msgs`; the document then quotes the pinned outputs as they
  are.
- A library form, for a function of the core or of Mathlib that readable definitions call (the
  worked example is `listLength`, `docs/KERNEL_DEF.md`, "A library form: `List.length`"; the
  measurements behind the present ones, `docs/library_forms/README.md`):
  1. its kernel form as a `kernel_def` with bare recursion, in the module of its type:
     `KernelDef/ListForms.lean` (lists, arrays, `Option`), `NatForms.lean`, `IntForms.lean`, or
     `MathlibForms.lean` for a function that needs more of Mathlib than the root imports (the
     root does not import it: every client pays for every import; measure the import cost of the
     root, a file `import KernelDef`, with `kernel_cost.py`, before and after);
  2. `@[kernel_rule] theorem foo_eq_listFoo : @List.foo α = listFoo` (or an equation on
     applications), proved with the readable equations. The left side is matched with reducible
     transparency, instances included: a rule at `ℕ` names the instances Lean synthesizes there
     (`instBEqOfDecidableEq instDecidableEqNat`, Mathlib's `Zero ℕ`). The compiler tries the rules
     of a head in the order they were declared, imported ones first: declare a rule at `ℕ` before
     a generic one, a specific one (`l[i]?.getD d`) before a general one (`o.getD d`), and a rule
     before the `kernel_def`s whose sources call its function (`log2` before `natSqrt`). The right
     side is translated again: it may be written in notation, and it must not call its own left
     side (it would be rewritten by itself);
  3. a test in `KernelDefTest/LibraryForms.lean` (or `NatForms.lean`, `IntForms.lean`,
     `MathlibForms.lean`): a source that calls the function, its `#print` under `#guard_msgs`,
     `#kernel_audit strict` on it, an `example` by `decide +kernel` on a nontrivial value;
  4. a bench pair: a generator in `scripts/gen_bench.py`, then `python3 scripts/gen_bench.py`;
  5. the gates: the term gate shows the new form as `NEW`, and any test definition that calls
     the function as `DIFFERENT`, as intended; then a new baseline.
- A bench check: a generator in `scripts/gen_bench.py` that writes both files, through `f` and
  through `Src.f`, on the same data drawn from a seeded generator, at three sizes (one theorem a
  size, so no statement repeats). Each file defines the `kernel_def`s of its check (a source that
  calls a library function, or one copied from ModularSymbolsTau with its namespaces mirrored
  under `KernelDefBench.<Check>`) and imports `KernelDef` only (`KernelDef.MathlibForms` too for
  a function of Mathlib). Add it to the list of `main`, run
  `python3 scripts/gen_bench.py`; the generator and the files go in the same change. Never edit a
  file of `bench/` by hand. The data as raw literals in a `noncomputable def`, sized so that the
  kernel's work shows over the file; the module docstring says what it measures.

## Measuring

- One heavy job at a time on this 32 GB machine, which is shared with ModularSymbolsTau work. A
  full `lake build`, `scripts/run_tests.sh` and a measurement run are heavy; a single module
  beside one is acceptable. Do not measure while something heavy runs elsewhere: the meter reads
  the whole machine's state.
- Instructions retired and peak memory are the measure, not wall time. Keep the minimum of
  repeated runs, and look at the spread (`kernel_cost.py noise`) before reading a difference.
- Put measurements and their write-ups in `docs/`: a folder per measurement, its rows (`*.jsonl`)
  and a README (question, answer, method, tables, what was not done, how to run it again). The
  baseline of the port is `docs/MEASURING.md`, "Baseline (2026-11-22)", its rows in
  `docs/baseline/` (tag `base`; the bench pairs of the library forms, tag `libforms`).

## Organization and style

- Every Lean, Python and shell file starts with the copyright header: Apache 2.0 (`LICENSE`),
  author Nicola Falciola. In Lean, before the imports:
  ```
  /-
  Copyright (c) 2026 Nicola Falciola. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Nicola Falciola
  -/
  ```
  In Python and shell, the same three lines as `#` comments, after the shebang line.
- A real module docstring at the top of every file (`/-! … -/`): what the file is for, its main
  definitions and results, its place.
- Mathlib naming: `lowerCamelCase` definitions, `snake_case` theorems, the `_eq`, `_iff`, `_of_`
  patterns.
- `fun x ↦`, not `fun x =>`. Projections of a product: `p.fst`, `p.snd`, never `p.1`, `p.2`;
  `.1`/`.2` stay on `∃`, `∧`, `↔`.
- Short proofs: once a proof compiles, try `simp`, `grind`, `omega`; `by exact t` is `t`; trim
  unused `simp` arguments as the linter advises.
- No heading comments inside a file (`/-! ### Title -/`): group declarations in named
  `section Name … end Name` blocks.
- Docstrings plain and concise, no bold, only where the name and the statement do not say it all.
- Kernel forms are written with `kernel_def`, not by hand; a helper that should not be a call in
  the kernel is a `@[kernel_inline] def`.
- Warning-clean and axiom-clean is preserved, never regressed.

## Shell and git

- Use `/usr/bin/grep` in pipelines: `grep` is aliased to ugrep, and a pipeline ending in it once
  stalled `lake build`.
- Commit only when asked.
