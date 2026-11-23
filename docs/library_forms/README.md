# Library forms: which functions of the core and of Mathlib get a kernel form (2026-11-22)

## The question

When a readable definition calls a function of a library (`l.foldl f b`, `l.sum`, `min a b`,
`n.log2`, `a + b` on `ℤ`, `decide (Nat.Prime p)`, …), the compiler keeps the call unless a
`@[kernel_rule]` gives it a kernel form, and the kernel then unfolds the library's definition at
every use: structural recursion through `brecOn`, instance chains, matchers, `Decidable`
instances, well-founded recursion. Which functions are worth a kernel form, and how much does
each buy?

## The answer

- **Five library functions are superlinear in the kernel, or run out of memory**; their kernel
  forms are linear or better. `Nat.log2` is no kernel primitive in Lean `v4.37.0-rc1` (57 k
  instructions a bit of its argument; the kernel form is 91 times cheaper at 2048 bits, and makes
  `Nat.sqrt` 51 times cheaper). `decide (Nat.Prime p)` is `O(p)` with growing memory (more than
  24 GB at `p = 16381`; the kernel form decides `p = 268435399` in 1.4 G). `List.max?` costs
  1339 G at `2^14` elements against 1.1 G. `Array.foldl` costs 150 G and 8.8 GB at `2^10`
  elements, more than 24 GB at `2^12`, against 0.06 G. `Nat.all` and `decide (∀ i < n, p i)` cost
  63 G and 33 G at `n = 4096` (more than 24 GB at 16384) against 0.23 G.
- **About twenty list functions gain 2.6 to 6.9 times per element**, the order of `List.length`
  against `listLength` (3.35 here): `arr[i]!`, `count`, `flatMap`, `lookup`, `flatten`, `sum`,
  `elem` / `contains` / `∈`, `reverse`, `Array.size`, `l[i]?`, `l[i]?.getD`, `l[i]!`, `foldl`,
  `find?`, `take`, `decide (l = r)` / `l == r`, `zipWith`, `drop`; and Mathlib's `Nat.fib` 4.6,
  `Nat.factorial` 2.3, `Nat.digits` 1.9.
- **The arithmetic of `ℤ` gains 22 to 389 k instructions a use** (`decide (a < b)` 389 k, `-`
  163 k, `decide (a = b)` 125 k, `+` 96 k, `/` 93 k, `*` 85 k, `%` 74 k). The core of
  `v4.37.0-rc1` ships the kernel forms with their proofs (`Init/Data/Int/Kernel.lean`,
  `Int.add_k`, …); the rules are one-liners. On `ℕ`, `Nat.testBit` (80 k), `min`, `max` (56 k),
  `Nat.pred` (42 k), `Nat.lcm` (36 k) and `Option.getD` (16 k) gain a use each.
- **No gain**: `==`, `!=`, `xor` on `Bool`; numerals of `ℤ`; `Nat.blt a b` against
  `Nat.ble (a + 1) b`.
- **All were made library forms**, but the last group: 31 new kernel forms and 52 new rules in
  `KernelDef/ListForms.lean`, `NatForms.lean`, `IntForms.lean` and the optional
  `MathlibForms.lean` (the library now has 42 kernel forms and 64 rules). The root's import cost
  does not move (6.434 G before, 6.443 G after).

## Method

**What the compiler handled.** One `kernel_def` per candidate, compiled with the compiler before
the new rules, then `#kernel_audit`: no finding means the compiler writes the call out already; a
miss (`list function`, `library function`, `instance`, `decide`) or `Int` means it keeps the call.
Already handled: `foldr`, `map`, `all`, `any`, `length`, `range`, `getD`, `headD`, `tail`,
`replicate`, `range'`, `eraseIdx`, `filter`, `++`, `zip`, `Nat.choose`; `decide (a = b)`, `≤`, `<`,
`a ∣ b`, `a ≡ b [MOD n]`, `Nat.Coprime`, `Nat.gcd` on `ℕ`; `&&`, `||`, `!`, `bif`, `!=` on `ℕ`.

**How each library function is defined** (read off its value: `brecOn`, `WellFounded`, matchers,
instances). Nearly every list function is structural recursion through `brecOn`; the searches go
through the `BEq` chain (`instBEqOfDecidableEq` → `decide` → `Nat.decEq` → `Nat.beq`); `min` and
`max` through `minOfLe`, an `ite` on `Nat.decLe`; the arithmetic of `ℤ` through matchers on the
constructors and `Int.subNatNat`; `Nat.sqrt.iter`, `Nat.digitsAux` and `Nat.minFacAux` through
`WellFounded.Nat.fix`. A `@[csimp]` lemma (`List.foldr` → `foldrTR`, `Nat.factorial` → binary
splitting) changes compiled code only: the kernel unfolds the definition.

**The kernel forms.** Each a `kernel_def` source, its rule and the proof (now in the modules of
`KernelDef/`); every rule was seen to fire in a `kernel_def` that calls the function, the audit
clean (`KernelDefTest/LibraryForms.lean`, `NatForms.lean`, `IntForms.lean`, `MathlibForms.lean`).

**The measurement** (`scripts/library_forms/libbench.py`). Files that import nothing (core only),
but those of Mathlib's functions, which import the four modules that define them, against a
baseline with the same imports. Each holds the kernel forms as the terms the compiler generated
(`Export.lean` prints them, fully explicit, and the files define them back), the data of one
candidate, and one `decide +kernel` check of the result (`Nat.beq r v = true`, `r = true`, or
`intBEq r v = true`, against the value computed in Python). The variants of a candidate differ
only in the checked expression:

- `lib`: what the compiler emits without the rule, the library call with its arguments compiled
  (a lambda `fun a x ↦ a + x` is already `fun a x ↦ Nat.add a x`);
- `kf`: what it emits with the rule;
- `base` (the data alone) is subtracted and, for a function that returns a list, `consumer`
  (`listSumNat` over the data), in proportion to the length of the result.

Each file runs in full and with `-Ddebug.skipKernelTC=true` (`scripts/techniques/technique_bench.py`);
the kernel's instructions and seconds are the difference. Heartbeats are read with
`IO.getNumHeartbeats` around the check (`Elab.async false`), in both runs: they count the
kernel's work (they count allocations), and their ratios follow the instruction ratios, usually
somewhat above them for the allocation-heavy library forms. Units: per element of the list (groups
`list`, `scalar`, `int`), per value (`log2`, `sqrt`: 256 values), per call (factorial, fib, digits,
prime). For `scalar` and `int` the unit is one step of a bare `List.rec` loop that uses the
operation once; "saved per use" is the cost of one use, the loop being the same in both.

Sizes: 256 to 16384 elements; values of 32 to 2048 bits; factorial of 256 to 16384; fib up to
65536; 64 to 16384 decimal digits; primes up to 65521 (`primeBig`: the kernel form alone, up to
268435399). Apple M5, 32 GB, Lean `v4.37.0-rc1`, one run a point. The rows are `results.jsonl`
(632) and every table `tables.txt` (`python3 scripts/library_forms/analyze.py`). The sweep was run
before the forms were added here, on the terms of the same compiler; the harness, as it is in
`scripts/library_forms/`, reproduces them (`pred`: 42.9 k a use against 42.5 k; `lcm`: 36.3 k
against 36.4 k). In the rows, `sqrt`'s `kf` is a form whose first guess still calls the slow
`Nat.log2`, and `kf_fastlog2` is `natSqrt` as the library has it.

## The ranked tables

"before → after" is library → kernel form, net of the data (and of the consumer for a list
result). Kernel G and heartbeats at the largest size measured with both; "handled" is whether the
compiler compiled the call before these forms.

### Class 1: the library function is superlinear, or fails

| # | function | handled | why the kernel is slow on it | size | net kernel G before → after | ratio | heartbeats (k) | peak GB |
|---|---|---|---|---:|---:|---:|---:|---:|
| 1 | `Nat.log2 n` | no (and the audit counted it as a primitive) | no primitive: its definition is a `Nat.rec` on the fuel `n` that halves `n` once a bit, about 57 k instructions a bit | 2048 bits ×256 | 30.19 → 0.33 | **91** (4.4 at 64 bits, 27 at 512) | 29,364 → 431 | 1.19 → 0.08 |
| 1b | `Nat.sqrt n` | no | `Nat.sqrt.iter` by `WellFounded.Nat.fix` (it reduces, through a fuel), `dite`, `let`, instance arithmetic; most of the cost is the `Nat.log2` of its first guess | 2048 bits ×256 | 30.74 → 0.60 (30.45 with the slow `log2`) | **51** (2.9 at 32 bits, 6.1 at 128, 18 at 512) | 30,120 → 643 | 1.22 → 0.09 |
| 2 | `decide (Nat.Prime p)` (Mathlib) | no (`decide` kept) | `Nat.decidablePrime` decides `∀ m, 2 ≤ m → m < p → ¬ m ∣ p`: `O(p)` steps, with memory that grows with `p` | `p` = 4093 | 33.26 → ~0.01 | ~5000 | 45,180 → 6 | 2.02 → 0.19 |
| | | | | `p` = 16381, 65521 | more than 24 GB → ≤ 0.01 | fails / works | — → 12, 25 | 24+ → 0.19 |
| | | | | `p` = 268435399 | not tried → 1.37 | | — → 1,606 | — → 0.28 |
| 3 | `List.max?` at `ℕ` | no | `foldl` (`brecOn`) of `max` = `maxOfLe` (`ite`, `Nat.decLe`), superlinear: 0.8, 2.7, 11.6, 81.7 M instructions an element at 256 … 16384. The accumulator occurs twice in `if acc ≤ x then x else acc` and the kernel does not find its value again; the kernel form's `Bool.rec x y (Nat.ble x y)` uses it twice too and is linear (the cause was not investigated further) | 16384 | 1338.77 (61 s) → 1.13 | **1184** | 3,494,905 → 1,418 | 0.30 → 0.18 |
| 4 | `Array.foldl` | no | `Array.foldlM` in `Id`: `dite` on `j < stop`, monad binds, `as[j]` a walk of `j` cells of `as.toList`, `as.size` a `List.length`; quadratic in time and memory | 1024 | 149.91 (15 s, 8.8 GB) → 0.06 | **2418** | 265,839 → 81 | 8.82 → 0.07 |
| | | | | 4096, 16384 | more than 24 GB (16384 stopped at 15.5 GB) → 0.26, 1.02 | fails / works | | |
| 5 | `Nat.all n fun i _ ↦ …` | no | `all (n+1) f = all n (fun i h ↦ f i _) && f n _`: the predicate is wrapped once a level, so evaluating it costs the depth; quadratic, with memory | 4096 | 63.45 (4.4 GB) → 0.23 | **270** | 118,433 → 280 | 4.38 → 0.09 |
| 5b | `decide (∀ i < n, p i)` | no (`decide` kept) | `Nat.decidableBallLT`, the same nesting | 4096 | 33.04 (1.9 GB) → 0.23 | **141** | 44,902 → 280 | 1.89 → 0.09 |
| | | | | 16384 | both more than 24 GB → 0.81 | fails / works | | |

### Class 2: linear, gain per element or per call

| # | function | why | per unit, k (before → after) | ratio | net G before → after | heartbeats (k) |
|---|---|---|---:|---:|---:|---:|
| 6 | `arr[i]!` (`Array`) | `Array.get!Internal` → `getD` → `dite` on `i < a.size` (`List.length`), `List.get` (`brecOn`) | 506.3 → 73.0 | **6.9** | 8.30 → 1.20 | 13,951 → 1,712 |
| 7 | `l.count a` at `ℕ` | `countP.go` (`brecOn`, accumulator), `bif`, the `BEq` chain, `HAdd` | 307.2 → 65.0 | **4.7** | 5.03 → 1.07 | 7,069 → 1,368 |
| 8 | `l.flatMap f` | `flatten (map f l)`: two `brecOn` walks, `++` an element | 832.4 → 180.2 | **4.6** | 13.64 → 2.95 | 21,362 → 4,128 |
| 9 | `Nat.fib n` (Mathlib) | `Nat.iterate` (`brecOn`) on pairs, `Prod` projections, `HAdd` | per call at 65536: 11.9 G → 2.6 G | **4.6** (heartbeats 5.7) | 11.95 → 2.58 | 15,336 → 2,687 |
| 10 | `l.lookup a`, `ℕ` keys | `brecOn`, two matchers, the `BEq` chain | 318.0 → 75.1 | **4.2** | 5.21 → 1.23 | 7,732 → 1,532 |
| 11 | `l.flatten` | `brecOn`, `List.append` (`brecOn`) | 263.9 → 68.3 | **3.9** | 4.32 → 1.12 | 6,720 → 1,542 |
| 12 | `l.sum` at `ℕ` | `foldr` (`brecOn`), `HAdd` an element | 183.8 → 52.4 | **3.5** (generic `listSum`: 2.65) | 3.01 → 0.86 | 4,433 → 1,188 |
| 13 | `l.elem a`, `l.contains a`, `decide (a ∈ l)` at `ℕ` | `brecOn`, matcher, the `BEq` chain | 220.3 → 63.2 | **3.5** (generic `listElem`: 2.33) | 3.61 → 1.04 | 5,402 → 1,319 |
| 14 | `l.reverse` | `reverseAux` (`brecOn`, accumulator) | 169.4 → 48.8 | **3.5** | 2.78 → 0.80 | 4,253 → 1,131 |
| 15 | `a.size` (`Array`) | `List.length` of `toList` | 176.4 → 51.8 | **3.4** | 2.89 → 0.85 | 4,408 → 1,205 |
| — | `l.length` (control; a rule since the port) | `brecOn`, `HAdd` | 174.5 → 52.1 | 3.35 (3.34 in `docs/techniques/length/`) | 2.86 → 0.85 | 4,379 → 1,188 |
| 16 | `l[i]!` (`List`) | `List.get!Internal` (`brecOn`), `Inhabited` | 234.3 → 73.1 | **3.2** | 3.84 → 1.20 | 6,278 → 1,696 |
| 17 | `l[i]?` | the `GetElem?` instance → `List.get?Internal` (`brecOn`) | 233.5 → 72.9 | **3.2** | 3.83 → 1.20 | 6,230 → 1,696 |
| 18 | `l[i]?.getD d` | the same and `Option.getD` (matcher) | 234.3 → 73.5 | **3.2** | 3.84 → 1.21 | 6,246 → 1,696 |
| 19 | `l.foldl f b` | `brecOn` (`List.foldl._f`, `below`) an element | 176.3 → 56.0 | **3.15** | 2.89 → 0.92 | 4,363 → 1,270 |
| 20 | `l.find? p` | `brecOn`, matcher on `p a` | 195.5 → 64.9 | **3.0** | 3.20 → 1.06 | 4,802 → 1,365 |
| 21 | `l.take n` | `brecOn`, matchers on two arguments | 216.3 → 73.8 | **2.9** | 3.54 → 1.21 | 5,243 → 1,704 |
| 22 | `decide (l = r)`, `l == r` at `List ℕ` | `List.hasDecEq` (`brecOn`, `Decidable` matchers, `Nat.decEq`), `List.beq` | 309.7 → 111.6 | **2.8** (`==`: 2.7) | 5.08 → 1.83 | 7,703 → 2,503 |
| 23 | `List.zipWith f l r` | `brecOn`, overlapping matcher | 293.0 → 109.9 | **2.7** | 4.80 → 1.80 | 7,136 → 2,532 |
| 24 | `l.drop n` | `brecOn`, matchers | 190.4 → 73.1 | **2.6** | 3.12 → 1.20 | 4,776 → 1,712 |
| 25 | `Nat.factorial n` (Mathlib) | `brecOn`, `HMul`, `succ` | per call at 16384: 2.4 G → 1.1 G | **2.3** (heartbeats 3.9) | 2.42 → 1.06 | 2,605 → 672 |
| 26 | `(l.map f).sum` | the `sum` | 235.0 → 104.8 | **2.2** (fused into one `List.rec`: 4.2, a fusion, not a rule) | 3.85 → 1.72 | 5,624 → 2,379 |
| 27 | `Nat.digits b n` (Mathlib) | `Nat.digitsAux` by `WellFounded.Nat.fix` (fuel `n + 1`, `Nat.eager`'s `ite`), matcher, `HMod`, `HDiv` | per call at 16384 digits: 5.0 G → 2.6 G | **1.9** (heartbeats 2.6) | 5.02 → 2.60 | 5,474 → 2,130 |

### Class 3: one use in a loop step (the loop the same in both)

| # | function | why | saved a use (k) | loop step, before → after (k) | net G at 16384 | heartbeats (k) |
|---|---|---|---:|---:|---:|---:|
| 28 | `decide (a < b)` on `ℤ` | `Int.decLt` = `decNonneg (b - (a + 1))`: `Int.sub`, `Int.add`, `Int.neg`, matchers | **389** | 489 → 100 | 8.01 → 1.64 | 10,784 → 2,052 |
| 29 | `a - b` on `ℤ` | `a + -b`: two matchers, `subNatNat`, `HAdd`/`HSub` on `ℕ` inside | **163** | 314 → 151 | 5.14 → 2.47 | 6,960 → 2,917 |
| 30 | `decide (a = b)` on `ℤ` | `Int.decEq`: two matchers, `decEq` on `ℕ`, `Decidable` constructors | **125** | 219 → 94 | 3.59 → 1.55 | 4,734 → 1,948 |
| 31 | `a + b` on `ℤ` | matcher, `subNatNat` (matcher), `HAdd` on `ℕ` | **96** | 214 → 118 | 3.51 → 1.94 | 4,885 → 2,418 |
| 32 | `a / b` on `ℤ` | matcher, `Neg`, `HDiv` on `ℕ` | **93** | 259 → 166 | 4.24 → 2.71 | 5,680 → 3,328 |
| 33 | `a * b` on `ℤ` | matcher, `negOfNat` (matcher), `HMul` | **85** | 253 → 168 | 4.15 → 2.76 | 5,531 → 3,340 |
| 34 | `Nat.testBit a k` | `bne`, `instBEqOfDecidableEq`, `HAnd`, `HShiftRight` | **80** | 158 → 79 | 2.59 → 1.29 | 3,412 → 1,680 |
| 35 | `a % b` on `ℤ` | matcher, `natAbs`, `subNatNat` | **74** | 217 → 142 | 3.55 → 2.33 | 4,638 → 2,913 |
| 36 | `min a b`, `max a b` on `ℕ` | `instMinNat` / `Nat.instMax` → `minOfLe` → `ite`, `Nat.decLe` | **56** | 121 → 65 | 1.99 → 1.06 | 2,649 → 1,403 |
| 37 | `-a` on `ℤ` | matcher, `negOfNat` (matcher) | **46** | 191 → 145 | 3.12 → 2.37 | 3,842 → 2,819 |
| 38 | `Nat.pred n` | matcher | **42** | 98 → 56 | 1.61 → 0.91 | 2,138 → 1,281 |
| 39 | `Nat.lcm a b` | `HDiv`, `HMul` (`gcd` is a primitive) | **36** | 103 → 67 | 1.69 → 1.09 | 2,300 → 1,467 |
| 40 | `a.natAbs` on `ℤ` | matcher | **22** | 93 → 71 | 1.53 → 1.17 | 1,979 → 1,481 |
| 41 | `o.getD d` (`Option`) | matcher | **16.5** | 83 → 67 | 1.36 → 1.09 | 1,893 → 1,495 |

### No gain, and not measured

| function | result |
|---|---|
| `a == b`, `a != b`, `xor a b` on `Bool` | 0.3 k a use (60.2 → 59.9 k a step): the chain to `Bool.decEq` is cheap. No rule. |
| numerals of `ℤ`, `(5 : ℤ)` against `Int.ofNat 5` | 0 (174.4 → 175.1 k a step): `instOfNat` is one unfolding. No rule. |
| `a < b` on `ℕ`: the compiler's `Nat.blt a b` against `Nat.ble (Nat.succ a) b`, `Nat.ble (a + 1) b`, or the branches swapped on `Nat.ble b a` | 6.1, 5.6, 8.8 k a use (8 to 14 %). Not a rule: a change of the translation of `<` at most. `Nat.blt` is not a primitive; it is one unfolding to `Nat.ble a.succ b` (`Nat.succ` of a literal is one). |
| `Nat.sqrt` with the slow `log2` | 1.01 to 1.40: the `log2` dominates; with `natLog2`, row 1b. |

Not measured, with the reason: `List.head?`, `List.isEmpty` and the other `O(1)` matchers (one
matcher a call, the order of `Option.getD`, 16 k); `Option.isSome`, `Option.map` (the same as
`Option.getD`); `Fin` (left out of evaluated code by the rules of kernel code); `Prod` projections
(representation, which the compiler keeps by design); `List.iota` (gone in this toolchain);
`List.prod` (the shape of `sum`); `List.min?`, `Nat.fold`, `Nat.any` (the shapes of `max?` and
`Nat.all`: expect the same, and the same kind of rule).

## What was added

| module | kernel forms | rules |
|---|---|---|
| `KernelDef/ListForms.lean` | `listFoldl`, `listSumNat`, `listSum`, `listReverseAux`, `listTake`, `listDrop`, `listZipWith`, `listFlatten`, `listFlatMap`, `listGet?`, `listFind?`, `listElemNat`, `listElem`, `listCountNat`, `listLookupNat`, `listMaxNat?`, `listBEqNat` (17) | `foldl`, `sum` (`ℕ`, generic), `reverseAux`, `reverse`, `take`, `drop`, `zipWith`, `flatten`, `flatMap`, `l[i]?`, `l[i]?.getD`, `l[i]!`, `default : ℕ`, `find?`, `elem` (`ℕ`, generic), `contains` (`ℕ`, generic), `count`, `lookup`, `max?`, `decide (l = r)`, `l == r`, `Array.foldl`, `a[i]!`, `Array.size`, `Option.getD` (28) |
| `KernelDef/NatForms.lean` | `log2Desc`, `log2Up`, `natLog2`, `sqrtIterFuel`, `natSqrt`, `natTestBit`, `natAll` (7) | `log2`, `sqrt`, `testBit`, `min`, `max`, `pred`, `lcm`, `Nat.all`, `decide (∀ i < n, p i)` (9) |
| `KernelDef/IntForms.lean` | `intBEq` (1) | `+`, `*`, `-`, unary `-`, `natAbs`, `%`, `/`, `toNat`, `decide (a < b)`, `decide (a ≤ b)`, `decide (a = b)` (11) |
| `KernelDef/MathlibForms.lean`, optional | `noDivFrom`, `natPrime`, `natFibAux`, `natFactorial`, `digitsFuel`, `natDigits` (6) | `decide (Nat.Prime p)`, `fib`, `factorial`, `digits` (4) |

31 kernel forms and 52 rules in all; with the 11 forms and 12 rules that `ListForms.lean` had, the
library has 42 kernel forms and 64 rules. The proofs are in the modules: an induction with
`simp` for most; `log2Desc_eq` (the invariant `(n = 0 ∧ r = 0) ∨ 2 ^ r ≤ n`,
`n < 2 ^ (r + 2 ^ k)`) and `log2Up_eq` for `natLog2`; `sqrtIterFuel_eq` (fuel above the guess)
for `natSqrt`; `noDivFrom_iff` with `Nat.prime_def_le_sqrt` for `natPrime`; `natFibAux_fib` for
`natFibAux`; `digitsFuel_eq` with `Nat.digits_def'` for `natDigits`. The forms of `ℤ` are the
core's, with its proofs (`Int.add_k_eq`, …).

`natLog2` doubles `k` until `n < 2 ^ 2 ^ k`, then finds the bits of `log2 n` from the top: `O(log
log n)` steps, each one shift of `n`; its fuel `n` is never exhausted. `natSqrt` is the core's
Newton iteration with the fuel the well-founded recursion uses (`guess + 1`) and its first guess
through `natLog2`. `natPrime` divides by `2, 3, …` up to `√p`.

The compiler itself changed in two places, neither of which changes a term (the term gate: the 38
earlier definitions that the change did not target are identical):

- `Nat.log2` is no longer in `kernelNatOps`, the primitives the audit accepts: a call of it in a
  kernel form is now reported (`KernelDefTest/NatForms.lean`, `plainLog2`).
- The audit lists a projection function of a structure that is not a class (`Array.toList`) as
  representation ("projections", like the primitive projection `.proj`), not as a library call:
  the criterion is `getProjectionFnInfo?` without `fromClass`.

## Edge cases

- **Instances.** A rule's left side is matched with reducible transparency, instances included.
  `List.sum` at `ℕ` is stated with the instances Lean elaborates under Mathlib (`instAddNat`,
  `MulZeroClass.toZero`); `List.elem`, `contains`, `count`, `lookup` at `ℕ` with
  `instBEqOfDecidableEq instDecidableEqNat`; `decide (l = r)` with `instDecidableEqList`;
  `min`, `max` with `instMinNat`, `Nat.instMax`. A source that elaborates other instance terms is
  not matched, and the audit reports the call. The generic forms (`listElem [BEq α]`,
  `listSum [Add α] [Zero α]`) keep the instance of their class: they save the `brecOn`, not the
  chain, and the audit reports their instance (pinned in `KernelDefTest/Audit.lean`).
- **Rule order.** The compiler tries the rules of a head in the order they were declared, imported
  ones first. The rules at `ℕ` come before the generic ones, `l[i]?.getD d` before `o.getD d`,
  and `log2` before the `kernel_def` of `natSqrt`, whose source calls `n.log2` (a `kernel_def` is
  compiled with the rules declared before it). A later rule never wins over an earlier one with
  the same head when both match.
- **A right side must not call its left side.** The compiler translates a rule's right side
  again, so it may be written in notation (`min a b = if a ≤ b then a else b`), but a right side
  that called its own left side would be rewritten by itself. `natLog2` bounds its search with a
  fuel instead of falling back to `Nat.log2`; `natDigits` writes out the bases `0` and `1`
  instead of calling `Nat.digits`.
- **Numeral patterns.** A first rule `Nat.digits (b + 2) n = digitsFuel (b + 2) (n + 1) n`
  matched `Nat.digits 10 n` by unifying `10` with `?b + 2`, and left `Nat.add 8 2` in the kernel
  form; `digits_eq_natDigits` is stated for every base.
- **Patterns with proofs.** `Nat.all n f` passes a proof of `i < n` to `f`: the rule's left side
  is `Nat.all n fun i _ ↦ f i`, which matches only when the body ignores the proof.
  `decide (∀ i < n, p i)` is matched through its instance `Nat.decidableBallLT` (with the
  predicate's instance as an argument of the rule). A predicate with an implication
  (`∀ i < n, i % 3 = 0 → i ≤ m`) compiles to `natAll`, but its `decide (a → b)` stays a `dite`.
- **Defaults.** `l[i]!` leaves `default`; the rule `default_eq_zero` makes it `0` at `ℕ`.
  `Array.foldl`'s rule is for its default bounds (`0`, `a.size`).
- **Universe polymorphism.** The list rules are universe polymorphic; the compiler instantiates
  their universes, and `zipWith` (three universes) fires.
- **Mathlib.** `Nat.Prime`, `Nat.fib`, `Nat.factorial`, `Nat.digits` need Mathlib to state; their
  module imports four modules of Mathlib (`import KernelDef.MathlibForms` costs 7.78 G, against
  6.44 G for `import KernelDef`), so the root does not import it.

## `Nat.log2`, and well-founded recursion

`Nat.log2` is no primitive of the kernel in `v4.37.0-rc1`. Probed on literals of 2000 to 8000
bits, `Nat.gcd`, `Nat.pow`, `Nat.blt`, `Nat.succ` and `Nat.pred` cost the same at every size,
`Nat.log2` grows with the bits (210, 324, 551 k heartbeats); `log2 (2 ^ 1000000)` took 830 G
instructions and 117 s. Its definition ("Lean assembly") is a `Nat.rec` on the fuel `n` with one
step a bit, each step a halving of `n` and a decrement of the fuel, a literal of the size of `n`.
The compiler's audit listed it among the primitives; it no longer does.

No library function needed a kernel form to be evaluated at all: the well-founded definitions on
`ℕ` (`Nat.sqrt.iter`, `Nat.digitsAux`, `Nat.minFacAux`) are compiled through
`WellFounded.Nat.fix` (`Init/WF.lean`), which "reduces on closed terms": a `Nat.rec` on the fuel
`h x + 1`, guarded by `Nat.eager`. They are slow, not stuck. What fails is memory: the four
quadratic cases of class 1 (`Array.foldl`, `Nat.all`, `decide (∀ i < n, …)`,
`decide (Nat.Prime p)`) reach a 24 GB cap at a few thousand elements.

## The bench pairs in the repository

`scripts/gen_bench.py` writes a pair for every function of class 1 and for some of classes 2 and
3: `bench/<Check>.lean` decides a check through the kernel form, `bench/<Check>Src.lean` through
`Src.f`, the library's function, at three sizes chosen so that the `Src` file takes a few seconds.
Kernel G, the minimum of three runs (`kernel_cost.py`, tag `libforms`, `docs/baseline/kcost.jsonl`;
heartbeats of the largest check, `heartbeats.py`, `docs/baseline/hb.jsonl`):

| check | sizes | kernel form | `Src.f` | ratio | peak GB (form / `Src`) | heartbeats, largest (form / `Src`) |
|---|---|---:|---:|---:|---:|---:|
| `Log2` | `2^13`, `2^14`, `2^15` bits | 0.011 | 4.077 | 364 | 0.156 / 0.413 | 13 / 1878 |
| `Sqrt` | `2^12`, `2^13`, `2^14` bits | 0.013 | 1.794 | 135 | 0.156 / 0.244 | 28 / 963 |
| `ListMax` | `2^8`, `2^9`, `2^10` elements | 0.182 | 4.905 | 27 | 0.167 / 0.175 | 119 / 9804 |
| `ArrayFoldl` | `2^6`, `2^7`, `2^8` | 0.048 | 12.311 | 259 | 0.158 / 0.711 | 34 / 16981 |
| `ForallLt` | `n` = `2^8`, `2^9`, `2^10` | 0.105 | 3.446 | 33 | 0.159 / 0.288 | 80 / 3391 |
| `Prime` | `p` = 251, 509, 1021 | 0.013 | 3.494 | 261 | 0.184 / 0.318 | 13 / 3432 |
| `Count` | `2^10`, `2^12`, `2^14` | 1.383 | 4.785 | 3.5 | 0.229 / 0.360 | 1383 / 5573 |
| `Sum` | `2^10`, `2^12`, `2^14` | 1.706 | 4.474 | 2.6 | 0.269 / 0.369 | 1402 / 4709 |
| `Reverse` | `2^10`, `2^12`, `2^14` | 1.369 | 3.957 | 2.9 | 0.273 / 0.353 | 1199 / 4337 |
| `IntLt` | `2^10`, `2^12`, `2^13` | 2.402 | 9.980 | 4.2 | 0.284 / 0.488 | 1676 / 8225 |
| `IntAdd` | `2^10`, `2^12`, `2^13` | 2.584 | 5.425 | 2.1 | 0.306 / 0.376 | 1759 / 4398 |
| `TestBit` | `2^10`, `2^12`, `2^14` | 2.317 | 8.352 | 3.6 | 0.277 / 0.459 | 1919 / 8281 |
| `Fib` | `n` = `2^12`, `2^14`, `2^15` | 1.758 | 8.871 | 5.0 | 0.315 / 0.520 | 1354 / 7679 |

A bench file also checks its data and its own `kernel_def`, the same in both files of a pair:
the kernel forms of class 1 cost nearly nothing beside them, and the ratios of classes 2 and 3
include that shared cost (the walk of `IntLt`, `IntAdd`, `TestBit` is a structural recursion in
`Src.f`, a bare recursor in the kernel form). The spread of three runs is at most 0.42 G
(`Log2`, whose files hold numbers of 32768 bits), elsewhere 0.12 G or less.

The import cost of the root, a file `import KernelDef` (`kernel_cost.py`, five runs, the
minimum; `import_cost.jsonl`): 6.434 G before the new modules, 6.443 G after (peak 0.153 GB both);
`import KernelDef.KernelForm` 2.989 G, unchanged; `import KernelDef.MathlibForms` 7.779 G.

## Running it again

```sh
lake build
python3 scripts/library_forms/libbench.py export          # the terms, into $KERNEL_DEF_WORK
TIME_LIMIT_S=300 python3 scripts/library_forms/libbench.py run docs/library_forms/results.jsonl
python3 scripts/library_forms/analyze.py docs/library_forms/results.jsonl > docs/library_forms/tables.txt
python3 scripts/gen_bench.py
REPEATS=3 python3 scripts/kernel_cost.py run OUT.jsonl TAG bench/Log2.lean bench/Log2Src.lean …
python3 scripts/heartbeats.py run OUT.jsonl TAG bench/Log2.lean bench/Log2Src.lean …
```

`libbench.py run` takes candidates or groups (`list`, `scalar`, `int`, `value`, `log2`,
`primeBig`) and resumes where it stopped; the whole sweep takes about 90 minutes, one heavy job at
a time. The library forms of `Array.foldl`, `Nat.all`, `decide (∀ i < n, …)` and
`decide (Nat.Prime p)` reach 24 GB at the largest sizes: lower `MEM_LIMIT_GB` on a shared machine.

## Files

- `results.jsonl`: the 632 rows of the sweep (candidate, group, variant, size, kernel G and
  seconds, elaboration G, peaks, heartbeats); `tables.txt`: every row net of the data, per unit,
  the ratio, and the summary at the largest size; `import_cost.jsonl`: the import cost of the
  root before and after, and of `KernelDef.MathlibForms`.
- `scripts/library_forms/libbench.py` (the sweep), `analyze.py` (the tables), `Export.lean` (the
  terms of the library forms, for the sweep).
