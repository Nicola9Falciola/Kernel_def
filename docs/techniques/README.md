# The kernel techniques, each measured against its absence

Each technique of the kernel playbook measured on its own, on synthetic Lean files that import
nothing (core Lean only; the re-run of `length/` imports `KernelDef`). The measurements were made
in ModularSymbolsTau, for its certificates, and copied here on 2026-11-22; the playbook is its
`CLAUDE.md` ("`decide` discipline") and `docs/CFSG_EXPERIMENTS.md`, E6 to E9 and E14 (E14 is
copied in `docs/history/E14.md`). Paths in the folders below other than their commands refer to
that repository. Every file runs in full and
with `-Ddebug.skipKernelTC=true` (`scripts/techniques/technique_bench.py`): the kernel's cost is the
difference, in instructions retired (the stable measure) and wall time (`docs/MEASURING.md`).

| technique | folder | the gain | where it matters |
|---|---|---|---|
| `nat_lit` in a `noncomputable def`, not `OfNat` numerals in a `def` | [`natlit/`](natlit/README.md) | **2.7×** less elaboration and 2.4× less memory for the data; the only form that elaborates 65536 literals | elaboration of the data; nothing in the kernel |
| the compiler's `listLength` (bare `List.rec`, `Nat.add`), not `List.length` | [`length/`](length/README.md) | **3.3×** in the kernel on `v4.37.0-rc1` (52 k against 175 k instructions per element; 3.69× in heartbeats) | every walk over a list |
| raw `Bool.rec` on `Nat.ble`, not `if` | [`branch/`](branch/README.md) | **3.9–6.1×** per branch (22.5 k against 88–137 k); `&&` costs 1.25× nested `Bool.rec`, `if … ∧ …` 4.5× | every test in a loop |
| walking a list with a counter, not indexing it in a loop | [`index/`](index/README.md) | indexing is quadratic in time and memory: **1550×** at 1000 values (`List.getD`, 120 G and 4.9 GB against 0.08 G), out of reach at 4000; `Array` is worse. A walk carrying an argument turns superlinear past about 32000 values (unexplained) | every loop over the data |
| a tree of rows, not one stack read by shifts | [`slotread/`](slotread/README.md) | a read of a stack of `n` rows copies half of it, so `n` reads are cubic in a level: **9.9 G and 0.5 GB** against about 19 GB at 3000 rows of 6750 bits; the tree is faster from 2000 rows on | the dual witness `Φᵀ` (not adopted yet) |
| inlining, not `let` | [`let/`](let/README.md) | **3–7 k** per binding (1.3–1.6×), even when the inlined value is used four times (the kernel's cache computes the copies once) | loop bodies |

The pattern behind `length`, `branch` and `let`: the kernel pays for every definition it unfolds (`brecOn`,
`ite`, `Decidable` instances, `HAdd`, matchers) and for every substitution (`let`, β), at every
evaluation, and caches only what is structurally equal. Its native operations on literals (`Nat.add`,
`Nat.ble`, `Nat.land`, …) and the bare recursors are the cheap path.

What `kernel_def` does with them. The compiler applies `branch` (`if`, `&&`, `match` become
`Bool.rec` and recursors), `let` (written out) and `length` (`l.length` and structural recursion
become a bare `List.rec`, `+` becomes `Nat.add`), and writes the numerals of a kernel form as raw
literals. `natlit` for the data, `index` (walk, do not index) and `slotread` (halving reads) stay
the author's: they change how the data is laid out or read, not notation or control flow
(`docs/KERNEL_DEF.md`, "What the compiler does not do").

Run one with `python3 scripts/techniques/run_<t>_bench.py run [OUT.jsonl]` (`OUT` defaults to
`docs/techniques/<t>/results.jsonl`), plot it with
`sage -python scripts/techniques/run_<t>_bench.py plot OUT.jsonl` (the plot needs matplotlib; the
CSV and the plot go next to `OUT.jsonl`). The files run with `lean`'s defaults, not the options
of `scripts/meter.py`, as in ModularSymbolsTau. Apple M5, 32 GB, Lean
`v4.36.0-rc2`, except `length/`, measured here on `v4.37.0-rc1` (2026-11-23).
