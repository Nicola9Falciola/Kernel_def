#!/usr/bin/env python3
# Copyright (c) 2026 Nicola Falciola. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Nicola Falciola
"""Writes the files of `bench/`: checks decided by the kernel on synthetic data, each in two files,
through the kernel form (`bench/<Check>.lean`) and through the readable definition `Src.f`
(`bench/<Check>Src.lean`), so that `scripts/kernel_cost.py` meters the two apart and a change of
the compiler shows as a change of the first.

    python3 scripts/gen_bench.py [OUT_DIR]

The checks, each at three sizes (one theorem a size), the data drawn from a seeded generator:

* `Shape`: `shapePk`, a walk of packed sparse rows (`m` rows of four entries);
* `HalvingRead`: `sumRd`, the sum of the `n` slots of a packed natural read one by one through the
  halving read `rdH` (its source calls `Src.rdH`, so `Src.sumRd` is readable down to the read);
* `RowProduct`: `e2RowsCheck`, `A · B = C` on dense packed rows checked row by row (`m × k` by
  `k × n`), its side conditions included;
* `Length`: `len`, whose source is `l.length`: `listLength` in the kernel form
  (`KernelDef/ListForms.lean`), core's `List.length` in `Src.len`; lists of `2^10`, `2^12`,
  `2^14` elements.

The library forms (`docs/library_forms/README.md`), each a source that calls a function of the
core or of Mathlib, decided through its kernel form (the rule's) and through `Src.f` (the
library's). The functions on which the library is superlinear, at sizes where `Src.f` still takes
a few seconds:

* `Log2`: `n.log2` (`natLog2`), on numbers of `2^13`, `2^14`, `2^15` bits;
* `Sqrt`: `n.sqrt` (`natSqrt`), on numbers of `2^12`, `2^13`, `2^14` bits;
* `ListMax`: `l.max?` (`listMaxNat?`), on lists of `2^8`, `2^9`, `2^10` elements;
* `ArrayFoldl`: `a.foldl (· + ·) 0` (`listFoldl` on `a.toList`), arrays of `2^6`, `2^7`, `2^8`;
* `ForallLt`: `decide (∀ i < n, i * i ≠ m)` (`natAll`), `n` of `2^8`, `2^9`, `2^10`;
* `Prime`: `decide (Nat.Prime p)` (`natPrime`, `KernelDef/MathlibForms.lean`), `p` = 251, 509,
  1021;

and some on which it is linear, `2^10`, `2^12`, `2^14` elements unless said otherwise:

* `Count`: `l.count 7` (`listCountNat`);
* `Sum`: `l.sum` (`listSumNat`);
* `Reverse`: `l.reverse.headD 0` (`listReverseAux`);
* `IntLt`: a count of the elements of a `List ℤ` below a bound, `if x < c` (`Int.blt'`), `2^10`,
  `2^12`, `2^13` elements;
* `IntAdd`: the sum of a `List ℤ` by structural recursion (`Int.add_k`), `2^10`, `2^12`, `2^13`;
* `TestBit`: a count of the elements with bit `3` set, `x.testBit 3` (`natTestBit`);
* `Fib`: `n.fib` (`natFibAux`, `KernelDef/MathlibForms.lean`), `n` = `2^12`, `2^14`, `2^15`.

Every file is self-contained: it imports `KernelDef` only and defines the `kernel_def`s of its
check, copied from ModularSymbolsTau (`Compute/Pack/Prim.lean`, `Compute/Pack/Walk.lean`,
`Compute/PackedMul.lean`, `Compute/PackedDense.lean`), with their namespaces mirrored so that the
terms are those of the source but for the names: the helpers of `RowProduct` that ModularSymbolsTau
keeps in other namespaces (`Pack`, `Packed`) are in `KernelDefBench.RowProduct.Pack`, opened.
`Src.f` is readable down to the definitions of its own namespace: the source of a `kernel_def` is
elaborated in the namespace `Src`, where the name of an earlier `kernel_def` of the same namespace
is its readable definition, and that of an opened one its kernel form. The files import the built
library (`lake build` first) and run in a few seconds.
"""

from __future__ import annotations

import random
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]

# The license header of every file written.
LICENSE_HEADER = """/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
"""

# The readable sources of the checks, from ModularSymbolsTau (docstrings shortened).
LEN_N = """/-- The length of a list (`Walk.lean`). -/
kernel_def lenN {α : Type*} : List α → ℕ
  | [] => 0
  | _ :: t => lenN t + 1
"""
SHAPE_SRC = LEN_N + """
/-- The entry count of the packed sparse row `r`, `PF = 2 ^ F`. -/
@[kernel_inline] def cnt (PF r : ℕ) : ℕ := r % PF

/-- The fields of the packed sparse row `r`. -/
@[kernel_inline] def flds (PF r : ℕ) : ℕ := r / PF

/-- Every column of the first `c` fields of `x` is below `k`. -/
kernel_def colsFieldsLt (PF PW k : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | c + 1, x => x % PF % PW < k && colsFieldsLt PF PW k c (x / PF)

/-- `A` has `m` rows and every column of every row is below `k`. -/
kernel_def shapePk (PF PW m k : ℕ) (A : List ℕ) : Bool :=
  lenN A == m && A.all fun r ↦ colsFieldsLt PF PW k (cnt PF r) (flds PF r)
"""
RDH_SRC = """/-- Slot `i` (of `Ks` bits, `MKs = 2 ^ Ks - 1`) of `x`, by `d` halvings and a plain read in a
block of eight slots. -/
kernel_def rdH (Ks MKs : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, x, i => MKs &&& (x >>> (Ks * i))
  | d + 1, x, i =>
    if 1 <<< (d + 3) ≤ i then
      rdH Ks MKs d (x >>> (Ks * (1 <<< (d + 3)))) (i - 1 <<< (d + 3))
    else
      rdH Ks MKs d (x &&& (1 <<< (Ks * (1 <<< (d + 3))) - 1)) i
"""
ROW_PACK_SRC = """/-- `2 ^ k`, as one shift (`Prim.lean`). -/
kernel_def pow2 (k : ℕ) : ℕ := 1 <<< k

/-- `2 ^ k − 1`: the mask of one `k`-bit slot. -/
kernel_def mask (k : ℕ) : ℕ := pow2 k - 1

/-- The sum of a list of naturals, one `Nat.add` per element. -/
kernel_def sumN : List ℕ → ℕ
  | [] => 0
  | x :: l => x + sumN l

/-- The naturals of a list as the slots of width `K` of one natural (`PackedMul.lean`). -/
kernel_def packNat (K : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: l => x + packNat K l <<< K

""" + LEN_N + """
/-- `∑_{j<k} 2^(K·j)`: a `1` in each of the first `k` slots of width `K`. -/
kernel_def ones (K k : ℕ) : ℕ := packNat K (List.replicate k 1)

/-- All `k` slots of `b` lie in `[lo, lo + t]`, by a handful of whole-row operations. -/
kernel_def swarOk (K k lo t b : ℕ) : Bool :=
  lo * ones K k ≤ b &&
    ((b - lo * ones K k) &&& 2 ^ (K - 1) * ones K k == 0 &&
      (b - lo * ones K k + (2 ^ (K - 1) - 1 - t) * ones K k) &&& 2 ^ (K - 1) * ones K k == 0)

/-- Every row passes the SWAR check on its first `k` slots, and there are at least `m` rows. -/
kernel_def rowsOk (K m k lo t : ℕ) (rows : List ℕ) : Bool :=
  m ≤ lenN rows && rows.all (swarOk K k lo t)

""" + RDH_SRC
ROW_SRC = """/-- The inputs of a product, as dense packed rows (`PackedDense.lean`). -/
kernel_def e2InOk (KA CA K CB m k n bA bB : ℕ) (A B : List ℕ) : Bool :=
  0 < KA && bA ≤ CA && 2 * bA < pow2 (KA - 1) && CA + bA < pow2 KA
    && 0 < K && bB ≤ CB && 2 * bB < pow2 (K - 1) && CB + bB < pow2 K
    && lenN A == m && lenN B == k
    && rowsOk KA m k (CA - bA) (2 * bA) A
    && rowsOk K k n (CB - bB) (2 * bB) B
    && B.all fun r ↦ r < pow2 (K * n)

/-- The target of a product, as dense packed rows. -/
kernel_def e2OutOk (K CC m n bC : ℕ) (C : List ℕ) : Bool :=
  bC ≤ CC && 2 * bC < pow2 (K - 1) && CC + bC < pow2 K
    && lenN C == m && rowsOk K m n (CC - bC) (2 * bC) C
    && C.all fun r ↦ r < pow2 (K * n)

/-- `∑ₜ u_{j+t} · Bs[t]`, `uᵢ` slot `i` of `a` read by `dA` halvings. -/
kernel_def dotH (KA MKA dA a : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x :: xs, j => rdH KA MKA dA a j * x + dotH KA MKA dA a xs (j + 1)

/-- `∑_{t<k} u_{j+t}`, `uᵢ` slot `i` of `a` read by `dA` halvings. -/
kernel_def slotSumH (KA MKA dA a : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, j => rdH KA MKA dA a j + slotSumH KA MKA dA a k (j + 1)

/-- The identity of a row `a` of `A` and the row `c` of `C`. -/
kernel_def rowEq (KA MKA dA CA k CB1 CC1 sB : ℕ) (Bs : List ℕ) (a c : ℕ) : Bool :=
  dotH KA MKA dA a Bs 0 + (k * CA * CB1 + CC1) == c + slotSumH KA MKA dA a k 0 * CB1 + CA * sB

/-- `rowEq` on the rows of `A` and of `C`, walked together. -/
kernel_def rowsEq (KA MKA dA CA k CB1 CC1 sB : ℕ) (Bs : List ℕ) : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: as, c :: cs =>
    rowEq KA MKA dA CA k CB1 CC1 sB Bs a c && rowsEq KA MKA dA CA k CB1 CC1 sB Bs as cs
  | _, _ => false

/-- `A · B = C` on dense packed rows, one row at a time. -/
kernel_def e2RowsCheck (KA MKA dA CA K CB CC m k n bA bB bC : ℕ) (A B C : List ℕ) :
    Bool :=
  e2InOk KA CA K CB m k n bA bB A B && e2OutOk K CC m n bC C
    && 2 * (k * bA * bB) < pow2 K && MKA == mask KA
    && rowsEq KA MKA dA CA k (CB * ones K n) (CC * ones K n) (sumN B) B A C
"""
HEAD = """/-!
# Bench: {title}{variant}

{what}

Generated by `scripts/gen_bench.py`; metered by `scripts/kernel_cost.py`, with
`bench/{other}.lean` the same check through {other_path}. Not a library: run it with `lean`.
-/
"""


def wrap(items, indent: str = "  ", width: int = 100) -> str:
    """`items` separated by commas, in lines of at most `width` characters where they fit."""
    items, lines, cur = list(items), [], indent
    for k, it in enumerate(items):
        piece = it + ("," if k + 1 < len(items) else "")
        if len(cur) + len(piece) + 1 > width and cur.strip():
            lines.append(cur.rstrip())
            cur = indent
        cur += piece + " "
    lines.append(cur.rstrip())
    return "\n".join(lines)


def header(title: str, src: bool, what: str, stem: str) -> str:
    return HEAD.format(title=title, variant=", readable" if src else ", kernel form", what=what,
                       other=stem if src else stem + "Src",
                       other_path="the kernel form" if src else "the readable definition")


def shape(src: bool) -> str:
    rng = random.Random(1)
    Wc, F, k, c = 9, 20, 400, 4
    PW, PF = 1 << Wc, 1 << F
    out = [header("a walk of packed sparse rows", src,
                  "`shapePk PF PW m k A`: `A` has `m` rows and every column is below `k`; "
                  "`m` rows\nof four entries.", "Shape"),
           "import KernelDef\n", "set_option maxRecDepth 100000\n",
           "namespace KernelDefBench.Shape\n", SHAPE_SRC]
    f = "Src.shapePk" if src else "shapePk"
    for m in (128, 512, 2048):
        rows = []
        for _ in range(m):
            flds = 0
            for j in range(c):
                col, sgn, mag = rng.randrange(k), rng.randrange(2), rng.randrange(1, 1 << 10)
                flds |= (col + PW * sgn + 2 * PW * mag) << (F * j)
            rows.append(c + PF * flds)
        out.append(f"/-- {m} rows. -/\nnoncomputable def rows{m} : List ℕ := [\n"
                   f"{wrap(map(str, rows))}]\n")
        out.append(f"theorem check{m} : {f} {PF} {PW} {m} {k} rows{m} = true := by\n"
                   "  decide +kernel\n")
    out.append("end KernelDefBench.Shape\n")
    return "\n".join(out)


def halving(src: bool) -> str:
    rng = random.Random(2)
    Ks = 16
    out = [header("the halving read", src,
                  "`sumRd Ks MKs d x n`: the sum of the `n` slots of `x`, read one by one by "
                  "`rdH` at the\ndepth `d` of `n` (the least with `2 ^ (d + 3) ≥ n`).",
                  "HalvingRead"),
           "import KernelDef\n", "namespace KernelDefBench.HalvingRead\n", RDH_SRC,
           "/-- The sum of the slots `0`, …, `n − 1` of `x`, each read by the halving read. -/\n"
           "kernel_def sumRd (Ks MKs d x : ℕ) : ℕ → ℕ\n"
           "  | 0 => 0\n"
           "  | i + 1 => Src.rdH Ks MKs d x i + sumRd Ks MKs d x i\n"]
    f = "Src.sumRd" if src else "sumRd"
    for n in (256, 1024, 4096):
        vals = [rng.randrange(1 << Ks) for _ in range(n)]
        x = sum(v << (Ks * i) for i, v in enumerate(vals))
        d = next(d for d in range(64) if (1 << (d + 3)) >= n)
        out.append(f"/-- {n} slots of {Ks} bits. -/\nnoncomputable def x{n} : ℕ :=\n  {x}\n")
        out.append(f"theorem check{n} : Nat.beq ({f} {Ks} {(1 << Ks) - 1} {d} x{n} {n}) "
                   f"{sum(vals)} = true := by\n  decide +kernel\n")
    out.append("end KernelDefBench.HalvingRead\n")
    return "\n".join(out)


def row_product(src: bool) -> str:
    rng = random.Random(3)
    KA, CA, bA, K, bB = 8, 100, 50, 21, 50
    CB = CC = 1 << 20
    out = [header("a product checked row by row", src,
                  "`e2RowsCheck`: `A · B = C` on dense packed rows (`m × k` by `k × n`), row by "
                  "row,\nwith its side conditions.", "RowProduct"),
           "import KernelDef\n", "set_option maxRecDepth 100000\n",
           "namespace KernelDefBench.RowProduct.Pack\n", ROW_PACK_SRC,
           "end KernelDefBench.RowProduct.Pack\n",
           "namespace KernelDefBench.RowProduct\n", "open KernelDefBench.RowProduct.Pack\n",
           ROW_SRC]
    f = "Src.e2RowsCheck" if src else "e2RowsCheck"
    for m, k, n in ((32, 16, 16), (64, 32, 32), (128, 32, 32)):
        A = [[rng.randint(-bA, bA) for _ in range(k)] for _ in range(m)]
        B = [[rng.randint(-bB, bB) for _ in range(n)] for _ in range(k)]
        C = [[sum(A[i][j] * B[j][l] for j in range(k)) for l in range(n)] for i in range(m)]
        bC = k * bA * bB

        def pack(row: list[int], width: int, bias: int) -> int:
            return sum((v + bias) << (width * t) for t, v in enumerate(row))
        dA = next(d for d in range(64) if (1 << (d + 3)) >= k)
        tag = f"{m}x{k}x{n}"
        for nm, rows in (("A", [pack(r, KA, CA) for r in A]), ("B", [pack(r, K, CB) for r in B]),
                         ("C", [pack(r, K, CC) for r in C])):
            out.append(f"noncomputable def {nm}{tag} : List ℕ := [\n{wrap(map(str, rows))}]\n")
        out.append(f"/-- `{m} × {k}` by `{k} × {n}`. -/\n"
                   f"theorem check{tag} : {f} {KA} {(1 << KA) - 1} {dA} {CA} {K} {CB} {CC} {m} {k} "
                   f"{n} {bA} {bB} {bC}\n    A{tag} B{tag} C{tag} = true := by\n  decide +kernel\n")
    out.append("end KernelDefBench.RowProduct\n")
    return "\n".join(out)


def length(src: bool) -> str:
    out = [header("the length of a list", src,
                  "`len l`, whose source is `l.length`: in its kernel form `listLength l` "
                  "(the rule "
                  "of\n`KernelDef/ListForms.lean`), in `Src.len` core's `List.length`. Lists of "
                  "`2^10`, `2^12`,\n`2^14` elements.", "Length"),
           "import KernelDef\n", "set_option maxRecDepth 100000\n",
           "namespace KernelDefBench.Length\n",
           "/-- The length of a list, through `List.length`. -/\n"
           "kernel_def len (l : List ℕ) : ℕ := l.length\n",
           "/-- An element: a constant, so that the data costs no instance. -/\n"
           "abbrev z : ℕ := nat_lit 0\n"]
    f = "Src.len" if src else "len"
    for e in (10, 12, 14):
        m = 1 << e
        out.append(f"/-- `2^{e}` elements. -/\nnoncomputable def rows{e} : List ℕ := [\n"
                   f"{wrap(['z'] * m)}]\n")
        out.append(f"theorem check{e} : Nat.beq ({f} rows{e}) {m} = true := by\n  decide +kernel\n")
    out.append("end KernelDefBench.Length\n")
    return "\n".join(out)


def lib_check(stem: str, title: str, what: str, defs: str, fname: str, cases: list[str],
              src: bool, imports: tuple[str, ...] = ("KernelDef",)) -> str:
    """A library form: the source `defs` (whose `kernel_def` `fname` calls the function), then each
    case, data and theorem, `{f}` standing for `fname` or `Src.fname`."""
    out = [header(title, src, what, stem), *[f"import {m}\n" for m in imports],
           "set_option maxRecDepth 100000\n", f"namespace KernelDefBench.{stem}\n", defs]
    f = f"Src.{fname}" if src else fname
    out += [c.replace("{f}", f) for c in cases]
    out.append(f"end KernelDefBench.{stem}\n")
    return "\n".join(out)


def nat_list(name: str, vals: list[int], doc: str) -> str:
    return f"/-- {doc} -/\nnoncomputable def {name} : List ℕ := [\n{wrap(map(str, vals))}]\n"


def int_list(name: str, vals: list[int], doc: str) -> str:
    return f"/-- {doc} -/\nnoncomputable def {name} : List ℤ := [\n{wrap(map(str, vals))}]\n"


def big(name: str, x: int, doc: str) -> str:
    """A numeral on one line: a numeral cannot be broken across lines."""
    return f"/-- {doc} -/\nnoncomputable def {name} : ℕ :=\n  {x}\n"


def nat_theorem(name: str, lhs: str, value: int) -> str:
    return f"theorem {name} : Nat.beq ({lhs}) {value} = true := by\n  decide +kernel\n"


def log2_check(src: bool) -> str:
    rng = random.Random(11)
    cases = []
    for e in (13, 14, 15):
        b = 1 << e
        x = rng.randrange(1 << (b - 1), 1 << b)
        cases += [big(f"x{e}", x, f"A number of `2^{e}` bits."),
                  nat_theorem(f"check{e}", f"{{f}} x{e}", b - 1)]
    return lib_check("Log2", "`Nat.log2`", src=src,
                     what="`lg n`, whose source is `n.log2`: `natLog2` in the kernel form "
                          "(`KernelDef/NatForms.lean`),\ncore's `Nat.log2`, one step a bit, in "
                          "`Src.lg`.",
                     defs="kernel_def lg (n : ℕ) : ℕ := n.log2\n", fname="lg", cases=cases)


def sqrt_check(src: bool) -> str:
    import math
    rng = random.Random(12)
    cases = []
    for e in (12, 13, 14):
        b = 1 << e
        x = rng.randrange(1 << (b - 1), 1 << b)
        cases += [big(f"x{e}", x, f"A number of `2^{e}` bits."),
                  nat_theorem(f"check{e}", f"{{f}} x{e}", math.isqrt(x))]
    return lib_check("Sqrt", "`Nat.sqrt`", src=src,
                     what="`isqrt n`, whose source is `n.sqrt`: `natSqrt` in the kernel form "
                          "(its first guess through\n`natLog2`), core's `Nat.sqrt` in "
                          "`Src.isqrt`.",
                     defs="kernel_def isqrt (n : ℕ) : ℕ := n.sqrt\n", fname="isqrt", cases=cases)


def list_max_check(src: bool) -> str:
    rng = random.Random(13)
    cases = []
    for e in (8, 9, 10):
        vals = [rng.randrange(1 << 16) for _ in range(1 << e)]
        cases += [nat_list(f"l{e}", vals, f"`2^{e}` elements."),
                  nat_theorem(f"check{e}", f"{{f}} l{e}", max(vals))]
    return lib_check("ListMax", "`List.max?`", src=src,
                     what="`maxOr l`, whose source is `l.max?.getD 0`: `listMaxNat?` in the kernel "
                          "form, core's\n`List.max?` (a `foldl` of `max` through `ite`, "
                          "superlinear in the kernel) in `Src.maxOr`.",
                     defs="kernel_def maxOr (l : List ℕ) : ℕ := l.max?.getD 0\n", fname="maxOr",
                     cases=cases)


def array_foldl_check(src: bool) -> str:
    rng = random.Random(14)
    cases = []
    for e in (6, 7, 8):
        vals = [rng.randrange(1 << 16) for _ in range(1 << e)]
        cases += [f"/-- `2^{e}` elements. -/\nnoncomputable def a{e} : Array ℕ := #[\n"
                  f"{wrap(map(str, vals))}]\n",
                  nat_theorem(f"check{e}", f"{{f}} a{e}", sum(vals))]
    return lib_check("ArrayFoldl", "`Array.foldl`", src=src,
                     what="`arrSum a`, whose source is `a.foldl (· + ·) 0`: `listFoldl` on "
                          "`a.toList` in the kernel\nform, core's `Array.foldl` (through "
                          "`Array.foldlM`, quadratic in the kernel) in `Src.arrSum`.",
                     defs="kernel_def arrSum (a : Array ℕ) : ℕ := a.foldl (· + ·) 0\n",
                     fname="arrSum", cases=cases)


def forall_lt_check(src: bool) -> str:
    cases = [f"theorem check{e} : {{f}} {1 << e} 7 = true := by\n  decide +kernel\n"
             for e in (8, 9, 10)]
    return lib_check("ForallLt", "a bounded `∀`", src=src,
                     what="`noSquare n m`, whose source is `decide (∀ i < n, i * i ≠ m)`: `natAll` "
                          "in the kernel form,\ncore's `Nat.decidableBallLT` (quadratic in the "
                          "kernel) in `Src.noSquare`.",
                     defs="kernel_def noSquare (n m : ℕ) : Bool := decide (∀ i < n, i * i ≠ m)\n",
                     fname="noSquare", cases=cases)


def prime_check(src: bool) -> str:
    cases = [f"theorem check{p} : {{f}} {p} = true := by\n  decide +kernel\n"
             for p in (251, 509, 1021)]
    return lib_check("Prime", "`Nat.Prime`", src=src,
                     imports=("KernelDef", "KernelDef.MathlibForms"),
                     what="`isPrime p`, whose source is `decide (Nat.Prime p)`: `natPrime` (trial "
                          "division to `√p`) in\nthe kernel form, Mathlib's `Nat.decidablePrime` "
                          "(every `m < p`) in `Src.isPrime`.",
                     defs="kernel_def isPrime (p : ℕ) : Bool := decide (Nat.Prime p)\n",
                     fname="isPrime", cases=cases)


def count_check(src: bool) -> str:
    rng = random.Random(15)
    cases = []
    for e in (10, 12, 14):
        vals = [rng.randrange(16) for _ in range(1 << e)]
        cases += [nat_list(f"l{e}", vals, f"`2^{e}` elements."),
                  nat_theorem(f"check{e}", f"{{f}} l{e}", vals.count(7))]
    return lib_check("Count", "`List.count`", src=src,
                     what="`sevens l`, whose source is `l.count 7`: `listCountNat` in the kernel "
                          "form, core's\n`List.count` in `Src.sevens`.",
                     defs="kernel_def sevens (l : List ℕ) : ℕ := l.count 7\n", fname="sevens",
                     cases=cases)


def sum_check(src: bool) -> str:
    rng = random.Random(16)
    cases = []
    for e in (10, 12, 14):
        vals = [rng.randrange(1 << 16) for _ in range(1 << e)]
        cases += [nat_list(f"l{e}", vals, f"`2^{e}` elements."),
                  nat_theorem(f"check{e}", f"{{f}} l{e}", sum(vals))]
    return lib_check("Sum", "`List.sum`", src=src,
                     what="`total l`, whose source is `l.sum`: `listSumNat` in the kernel form, "
                          "core's `List.sum`\nin `Src.total`.",
                     defs="kernel_def total (l : List ℕ) : ℕ := l.sum\n", fname="total",
                     cases=cases)


def reverse_check(src: bool) -> str:
    rng = random.Random(17)
    cases = []
    for e in (10, 12, 14):
        vals = [rng.randrange(1 << 16) for _ in range(1 << e)]
        cases += [nat_list(f"l{e}", vals, f"`2^{e}` elements."),
                  nat_theorem(f"check{e}", f"{{f}} l{e}", vals[-1])]
    return lib_check("Reverse", "`List.reverse`", src=src,
                     what="`lastOf l`, whose source is `l.reverse.headD 0`: `listReverseAux` in "
                          "the kernel form, core's\n`List.reverse` in `Src.lastOf`.",
                     defs="kernel_def lastOf (l : List ℕ) : ℕ := l.reverse.headD 0\n",
                     fname="lastOf", cases=cases)


def int_lt_check(src: bool) -> str:
    rng = random.Random(18)
    cases = []
    for e in (10, 12, 13):
        vals = [rng.randrange(-(1 << 15), 1 << 15) for _ in range(1 << e)]
        cases += [int_list(f"l{e}", vals, f"`2^{e}` elements."),
                  nat_theorem(f"check{e}", f"{{f}} 100 l{e}", sum(1 for v in vals if v < 100))]
    defs = ("/-- The elements of `l` below `c`. -/\n"
            "kernel_def countBelow (c : ℤ) : List ℤ → ℕ\n"
            "  | [] => 0\n"
            "  | x :: l => (if x < c then 1 else 0) + countBelow c l\n")
    return lib_check("IntLt", "`<` on `ℤ`", src=src,
                     what="`countBelow c l`, a count of the elements of `l` below `c`: `Int.blt'` "
                          "in the kernel form,\n`Int.decLt` (through `Int.sub`, `Int.add`, a "
                          "matcher) in `Src.countBelow`.",
                     defs=defs, fname="countBelow", cases=cases)


def int_add_check(src: bool) -> str:
    rng = random.Random(19)
    cases = []
    for e in (10, 12, 13):
        vals = [rng.randrange(-(1 << 15), 1 << 15) for _ in range(1 << e)]
        cases += [int_list(f"l{e}", vals, f"`2^{e}` elements."),
                  f"theorem check{e} : {{f}} l{e} = {sum(vals)} := by\n  decide +kernel\n"]
    defs = ("/-- The sum of a list of integers. -/\n"
            "kernel_def intTotal : List ℤ → ℤ\n"
            "  | [] => 0\n"
            "  | x :: l => x + intTotal l\n")
    return lib_check("IntAdd", "`+` on `ℤ`", src=src,
                     what="`intTotal l`, the sum of a list of integers: `Int.add_k` in the kernel "
                          "form, `Int.add`\n(matchers, `Int.subNatNat`) in `Src.intTotal`.",
                     defs=defs, fname="intTotal", cases=cases)


def test_bit_check(src: bool) -> str:
    rng = random.Random(20)
    cases = []
    for e in (10, 12, 14):
        vals = [rng.randrange(1 << 16) for _ in range(1 << e)]
        cases += [nat_list(f"l{e}", vals, f"`2^{e}` elements."),
                  nat_theorem(f"check{e}", f"{{f}} l{e}", sum(1 for v in vals if v >> 3 & 1))]
    defs = ("/-- The elements of `l` with bit `3` set. -/\n"
            "kernel_def countBit : List ℕ → ℕ\n"
            "  | [] => 0\n"
            "  | x :: l => (if x.testBit 3 then 1 else 0) + countBit l\n")
    return lib_check("TestBit", "`Nat.testBit`", src=src,
                     what="`countBit l`, a count of the elements of `l` with bit `3` set: "
                          "`natTestBit` in the kernel\nform, core's `Nat.testBit` (`bne` and the "
                          "instance chains) in `Src.countBit`.",
                     defs=defs, fname="countBit", cases=cases)


def fib_check(src: bool) -> str:
    cases = []
    for e in (12, 14, 15):
        a, b = 0, 1
        for _ in range(1 << e):
            a, b = b, a + b
        cases += [big(f"f{e}", a, f"`fib (2^{e})`."),
                  f"theorem check{e} : Nat.beq ({{f}} {1 << e}) f{e} = true := by\n"
                  "  decide +kernel\n"]
    return lib_check("Fib", "`Nat.fib`", src=src, imports=("KernelDef", "KernelDef.MathlibForms"),
                     what="`fibOf n`, whose source is `n.fib`: `natFibAux` in the kernel form, "
                          "Mathlib's `Nat.fib`\n(`Nat.iterate` on pairs) in `Src.fibOf`.",
                     defs="kernel_def fibOf (n : ℕ) : ℕ := n.fib\n", fname="fibOf", cases=cases)


def main() -> None:
    out = Path(sys.argv[1]) if len(sys.argv) > 1 else REPO / "bench"
    out.mkdir(parents=True, exist_ok=True)
    for stem, gen in (("Shape", shape), ("HalvingRead", halving), ("RowProduct", row_product),
                      ("Length", length), ("Log2", log2_check), ("Sqrt", sqrt_check),
                      ("ListMax", list_max_check), ("ArrayFoldl", array_foldl_check),
                      ("ForallLt", forall_lt_check), ("Prime", prime_check),
                      ("Count", count_check), ("Sum", sum_check), ("Reverse", reverse_check),
                      ("IntLt", int_lt_check), ("IntAdd", int_add_check),
                      ("TestBit", test_bit_check), ("Fib", fib_check)):
        for src in (False, True):
            lines = gen(src).split("\n")
            imports = [ln for ln in lines if ln.startswith("import ")]
            body = "\n".join(ln for ln in lines if not ln.startswith("import ")).lstrip("\n")
            (out / f"{stem}{'Src' if src else ''}.lean").write_text(
                LICENSE_HEADER + "\n".join(imports) + "\n\n" + body)
    print("bench files written to", out)


if __name__ == "__main__":
    main()
