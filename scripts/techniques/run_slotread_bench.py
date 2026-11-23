#!/usr/bin/env python3
# Copyright (c) 2026 Nicola Falciola. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Nicola Falciola
"""Random access to the rows of the dual witness, in the kernel, on synthetic files that import
nothing: the read pattern of `relKillsQ` (ModularSymbolsTau, `Compute/Pack/DualQ.lean`), which holds the memory of a
level's `Basis.lean` (`docs/techniques/slotread/README.md`).

Each file holds `n` rows `r_c` of `Ks = K g` bits (`g = n / 12`, `K = 27`: a row of `Φᵀ` at a prime
level with `n` points) and two permutations `σ`, `τ` of the points as packed tables, with
`r_c + r_{σ c} = 2 Cs` and `r_c + r_{τ c} + r_{τ² c} = 3 Cs` for every `c`; one `decide +kernel`
checks both at every point, with five reads of a row per point, as `relKillsQ` does. The variants
differ in where the rows are and how row `i` is read:

| variant   | the rows                                   | a read                                      |
|-----------|--------------------------------------------|---------------------------------------------|
| `stack`   | one natural of `n` slots (the levels' format, E12) | a shift of the stack and a mask     |
| `split<k>`| the same stack, the points in `k` theorems | the same                                    |
| `nth`     | a list of `n` rows                         | a walk of `i` cells (bare `List.rec`)       |
| `list2`   | a list of lists, `√n` rows each            | two walks of at most `√n` cells             |
| `list3`   | three levels of lists, `∛n` each           | three walks of at most `∛n` cells           |
| `halve`   | the same stack, nothing else               | `log₂ n` halvings of the stack, each half computed once by the kernel and found again in its cache |
| `tree`    | a perfect binary tree of rows              | `log₂ n` steps, one comparison each         |
| `tree4`   | a perfect 4-ary tree of rows               | `log₄ n` steps, two bits of `i` each        |
| `block<B>`| a list of `B` naturals, `n / B` slots each | a walk of at most `B` cells, then a shift of a block |

A run is capped by `TIME_LIMIT_S` (default here 600 s) and `MEM_LIMIT_GB` (default here 6); a
variant killed at one size is not run at the larger ones.

Usage: python3 scripts/techniques/run_slotread_bench.py run [OUT.jsonl] [n ...] [variants=v,v]
       sage -python scripts/techniques/run_slotread_bench.py plot [OUT.jsonl]    (CSV and plot next to OUT)
"""

from __future__ import annotations

import math
import os
import random
import sys
from pathlib import Path

os.environ.setdefault("TIME_LIMIT_S", "600")
os.environ.setdefault("MEM_LIMIT_GB", "6")
sys.path.insert(0, str(Path(__file__).resolve().parent))
from technique_bench import (append, done, load, measure, out_and_args, style,  # noqa: E402
                             write_csv)

NS = [996, 1500, 2004, 3000, 4002, 6000]
VARIANTS = ["stack", "split16", "halve", "nth", "list2", "list3", "tree", "tree4", "block32"]
K = 27
CD = 1 << 25
BND = 1 << 20


def model(n: int):
    """Rows and permutations with the two relations: the points in groups of six
    `a₁ a₂ a₃ b₁ b₂ b₃`, `τ = (a₁ a₂ a₃)(b₁ b₂ b₃)`, `σ = (a₁ b₁)(a₂ b₂)(a₃ b₃)`,
    `φ(a₃) = −φ(a₁) − φ(a₂)`, `φ(b_i) = −φ(a_i)`, then the points relabelled at random."""
    assert n % 6 == 0
    rng = random.Random(n)
    g = max(1, n // 12)
    lab = list(range(n))
    rng.shuffle(lab)
    sig, tau, phi = [0] * n, [0] * n, [None] * n
    for q in range(n // 6):
        a = [lab[6 * q + i] for i in range(3)]
        b = [lab[6 * q + 3 + i] for i in range(3)]
        f1 = [rng.randrange(-BND, BND + 1) for _ in range(g)]
        f2 = [rng.randrange(-BND, BND + 1) for _ in range(g)]
        f3 = [-x - y for x, y in zip(f1, f2)]
        for i, f in enumerate((f1, f2, f3)):
            phi[a[i]] = f
            phi[b[i]] = [-x for x in f]
            sig[a[i]], sig[b[i]] = b[i], a[i]
            tau[a[i]], tau[b[i]] = a[(i + 1) % 3], b[(i + 1) % 3]
    rows = [sum((CD + x) << (K * j) for j, x in enumerate(f)) for f in phi]
    cs = sum(CD << (K * j) for j in range(g))
    return g, rows, sig, tau, cs


def lit(v: int) -> str:
    return f"nat_lit 0x{v:x}"


DEFS = """set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option linter.unusedVariables false

/-- `l[j]`, or 0 past the end: a bare `List.rec`, the position counted down by `Nat.beq`. -/
noncomputable def nthQ (l : List Nat) : Nat → Nat :=
  @List.rec Nat (fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ r j => @Bool.rec (fun _ => Nat) (r (Nat.sub j (nat_lit 1))) x (Nat.beq j (nat_lit 0))) l

noncomputable def nthL (l : List (List Nat)) : Nat → List Nat :=
  @List.rec (List Nat) (fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ r j => @Bool.rec (fun _ => List Nat) (r (Nat.sub j (nat_lit 1))) x
      (Nat.beq j (nat_lit 0))) l

noncomputable def nthLL (l : List (List (List Nat))) : Nat → List (List Nat) :=
  @List.rec (List (List Nat)) (fun _ => Nat → List (List Nat)) (fun _ => [])
    (fun x _ r j => @Bool.rec (fun _ => List (List Nat)) (r (Nat.sub j (nat_lit 1))) x
      (Nat.beq j (nat_lit 0))) l

/-- Slot `i` of `x`, a number of `2 ^ d` slots of `Ks` bits, by halving: at each level the low
half (a mask) or the high half (a shift) of the number above. The term of a half is the same at
every read that goes through it, so the kernel computes each half once and keeps it: the stack
becomes a binary tree of naturals in the kernel's cache, with no other data than the stack. -/
noncomputable def rdH (Ks : Nat) : Nat → Nat → Nat → Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat) (fun x _ => x)
    (fun d ih x i =>
      @Bool.rec (fun _ => Nat)
        (ih (Nat.land x (Nat.sub (Nat.shiftLeft (nat_lit 1)
          (Nat.mul Ks (Nat.shiftLeft (nat_lit 1) d))) (nat_lit 1))) i)
        (ih (Nat.shiftRight x (Nat.mul Ks (Nat.shiftLeft (nat_lit 1) d)))
          (Nat.sub i (Nat.shiftLeft (nat_lit 1) d)))
        (Nat.ble (Nat.shiftLeft (nat_lit 1) d) i))

inductive BT where
  | leaf : Nat → BT
  | node : BT → BT → BT

/-- Row `i` of a perfect binary tree whose left subtree has `h` leaves. -/
noncomputable def getT : BT → Nat → Nat → Nat :=
  @BT.rec (fun _ => Nat → Nat → Nat) (fun a _ _ => a)
    (fun _ _ l r h i => @Bool.rec (fun _ => Nat) (l (Nat.shiftRight h (nat_lit 1)) i)
      (r (Nat.shiftRight h (nat_lit 1)) (Nat.sub i h)) (Nat.ble h i))

inductive QT where
  | leaf : Nat → QT
  | node : QT → QT → QT → QT → QT

/-- Row `i` of a perfect 4-ary tree: `s` is twice the number of levels below the root, and the two
bits of `i` at `s - 2` choose the child. -/
noncomputable def getQ : QT → Nat → Nat → Nat :=
  @QT.rec (fun _ => Nat → Nat → Nat) (fun a _ _ => a)
    (fun _ _ _ _ c0 c1 c2 c3 s i =>
      @Bool.rec (fun _ => Nat)
        (@Bool.rec (fun _ => Nat) (c0 (Nat.sub s (nat_lit 2)) i) (c1 (Nat.sub s (nat_lit 2)) i)
          (Nat.beq (Nat.land (Nat.shiftRight i (Nat.sub s (nat_lit 2))) (nat_lit 1)) (nat_lit 1)))
        (@Bool.rec (fun _ => Nat) (c2 (Nat.sub s (nat_lit 2)) i) (c3 (Nat.sub s (nat_lit 2)) i)
          (Nat.beq (Nat.land (Nat.shiftRight i (Nat.sub s (nat_lit 2))) (nat_lit 1)) (nat_lit 1)))
        (Nat.beq (Nat.land (Nat.shiftRight i (Nat.sub s (nat_lit 1))) (nat_lit 1)) (nat_lit 1)))
"""


def bt(rows: list[int]) -> str:
    if len(rows) == 1:
        return f"BT.leaf ({lit(rows[0])})"
    h = len(rows) // 2
    return f"BT.node ({bt(rows[:h])}) ({bt(rows[h:])})"


def qt(rows: list[int]) -> str:
    if len(rows) == 1:
        return f"QT.leaf ({lit(rows[0])})"
    q = len(rows) // 4
    return "QT.node " + " ".join(f"({qt(rows[i * q:(i + 1) * q])})" for i in range(4))


def chunks(xs: list, s: int) -> list[list]:
    return [xs[i:i + s] for i in range(0, len(xs), s)]


def lst(xs: list[int]) -> str:
    return "[" + ", ".join(lit(x) for x in xs) + "]"


def stack_def(name: str, rows: list[int], ks: int) -> str:
    """The stack as a balanced sum of shifted literals of at most 8 rows: one long literal would
    take the elaborator quadratic time to read, and a chain of sums would make the kernel hold
    every partial sum. The kernel builds it once, in about `log₂ n` copies of the stack."""
    def term(rs: list[int]) -> str:
        if len(rs) <= 8:
            return lit(sum(r << (ks * i) for i, r in enumerate(rs)))
        h = len(rs) // 2
        return (f"Nat.lor ({term(rs[:h])}) (Nat.shiftLeft ({term(rs[h:])}) "
                f"(nat_lit {ks * h}))")
    return f"noncomputable def {name} : Nat := {term(rows)}"


def source(n: int, variant: str) -> str:
    g, rows, sig, tau, cs = model(n)
    ks = K * g
    mks = (1 << ks) - 1
    wt = max(1, (n - 1).bit_length())
    mw = (1 << wt) - 1
    tab = lambda p: sum(v << (wt * c) for c, v in enumerate(p))  # noqa: E731
    tt = [tau[tau[c]] for c in range(n)]
    data = [f"noncomputable def SG : Nat := {lit(tab(sig))}",
            f"noncomputable def TG : Nat := {lit(tab(tau))}",
            f"noncomputable def TTG : Nat := {lit(tab(tt))}"]
    rd = lambda t, j: (f"Nat.land (nat_lit {mw}) "  # noqa: E731
                       f"(Nat.shiftRight {t} (Nat.mul (nat_lit {wt}) ({j})))")
    split = 1
    if variant == "stack" or variant.startswith("split"):
        split = int(variant[5:]) if variant.startswith("split") else 1
        data.append(stack_def("STK", rows, ks))
        get = lambda j: (f"Nat.land ({lit(mks)}) (Nat.shiftRight STK "  # noqa: E731
                         f"(Nat.mul (nat_lit {ks}) ({j})))")
    elif variant == "halve":
        d = max(1, (n - 1).bit_length())
        data.append(stack_def("STK", rows, ks))
        get = lambda j: f"rdH (nat_lit {ks}) (nat_lit {d}) STK ({j})"  # noqa: E731
    elif variant == "nth":
        data.append(f"noncomputable def ROWS : List Nat := {lst(rows)}")
        get = lambda j: f"nthQ ROWS ({j})"  # noqa: E731
    elif variant == "list2":
        s = math.isqrt(n - 1) + 1
        data.append("noncomputable def ROWS : List (List Nat) := ["
                    + ", ".join(lst(c) for c in chunks(rows, s)) + "]")
        get = lambda j: (f"nthQ (nthL ROWS (Nat.div ({j}) (nat_lit {s}))) "  # noqa: E731
                         f"(Nat.mod ({j}) (nat_lit {s}))")
    elif variant == "list3":
        s = round(n ** (1 / 3))
        while s ** 3 < n:
            s += 1
        data.append("noncomputable def ROWS : List (List (List Nat)) := ["
                    + ", ".join("[" + ", ".join(lst(c) for c in chunks(b, s)) + "]"
                                for b in chunks(rows, s * s)) + "]")
        get = lambda j: (f"nthQ (nthL (nthLL ROWS (Nat.div ({j}) (nat_lit {s * s}))) "  # noqa: E731
                         f"(Nat.div (Nat.mod ({j}) (nat_lit {s * s})) (nat_lit {s}))) "
                         f"(Nat.mod ({j}) (nat_lit {s}))")
    elif variant == "tree":
        d = max(1, (n - 1).bit_length())
        data.append(f"noncomputable def TREE : BT := {bt(rows + [0] * ((1 << d) - n))}")
        get = lambda j: f"getT TREE (nat_lit {1 << (d - 1)}) ({j})"  # noqa: E731
    elif variant == "tree4":
        d = 1
        while 4 ** d < n:
            d += 1
        data.append(f"noncomputable def TREE : QT := {qt(rows + [0] * (4 ** d - n))}")
        get = lambda j: f"getQ TREE (nat_lit {2 * d}) ({j})"  # noqa: E731
    elif variant.startswith("block"):
        nb = int(variant[5:])
        s = -(-n // nb)
        data.append("noncomputable def BLK : List Nat := ["
                    + ", ".join(lit(sum(r << (ks * i) for i, r in enumerate(c)))
                                for c in chunks(rows, s)) + "]")
        get = lambda j: (f"Nat.land ({lit(mks)}) (Nat.shiftRight "  # noqa: E731
                         f"(nthQ BLK (Nat.div ({j}) (nat_lit {s}))) "
                         f"(Nat.mul (nat_lit {ks}) (Nat.mod ({j}) (nat_lit {s}))))")
    else:
        raise SystemExit(f"unknown variant {variant}")

    def body(c: str) -> str:
        two = f"Nat.beq (Nat.add ({get(c)}) ({get(rd('SG', c))})) ({lit(2 * cs)})"
        three = (f"Nat.beq (Nat.add (Nat.add ({get(c)}) ({get(rd('TG', c))})) "
                 f"({get(rd('TTG', c))})) ({lit(3 * cs)})")
        return (f"@Bool.rec (fun _ => Bool) Bool.false\n"
                f"        (@Bool.rec (fun _ => Bool) Bool.false ih\n          ({three}))\n"
                f"        ({two})")

    thms = []
    step = -(-n // split)
    for k in range(split):
        lo, m = k * step, min(step, n - k * step)
        pt = "c" if lo == 0 else f"Nat.add (nat_lit {lo}) c"
        thms.append(f"theorem check{k} : @Nat.rec (fun _ => Bool) Bool.true\n"
                    f"    (fun c ih =>\n      {body(pt)}) (nat_lit {m}) = true := by\n"
                    f"  decide +kernel\n")
    return (f"/-! Slot-read benchmark, variant `{variant}`, {n} rows of {ks} bits. Generated by\n"
            f"`scripts/techniques/run_slotread_bench.py`. -/\n{DEFS}\n" + "\n\n".join(data) + "\n\n"
            + "\n".join(thms))


def run(out: Path, ns: list[int], variants: list[str]) -> None:
    rows = load(out) if out.exists() else []
    have = done(out, "variant", "n")
    dead = {r["variant"] for r in rows if "error" in r}
    for n in ns:
        for v in variants:
            if (v, n) in have or v in dead:
                continue
            g = max(1, n // 12)
            row = {"variant": v, "n": n, "g": g, "row_bits": K * g, "stack_MB": n * K * g / 8e6}
            try:
                row |= measure(source(n, v))
            except RuntimeError as e:
                msg = str(e)
                row["error"] = (msg.splitlines()[0] if msg.startswith("kernel:") else
                                next((ln for ln in msg.splitlines() if "error" in ln), msg))[:300]
                dead.add(v)
            append(out, row)


COLORS = {"stack": "#e34948", "split16": "#eb6834", "halve": "#0b8a5a", "nth": "#8a8a84", "list2": "#eda100",
          "list3": "#c4a000", "tree": "#2a78d6", "tree4": "#6250d6", "block32": "#1baf7a"}


def plot(out: Path) -> None:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    rows = load(out)
    write_csv(rows, out.parent / "results.csv")
    ok = [r for r in rows if "error" not in r]
    fig, axs = plt.subplots(1, 3, figsize=(16, 5.6), dpi=150)
    panels = [("kernel_G", "Kernel instructions", "billions"), ("kernel_s", "Kernel time", "s"),
              ("peak_GB", "Peak memory", "GB")]
    for ax, (key, title, ylabel) in zip(axs, panels):
        for v in dict.fromkeys(r["variant"] for r in ok):
            pts = sorted((r["n"], r[key]) for r in ok if r["variant"] == v and r[key] > 0)
            if pts:
                ax.plot(*zip(*pts), color=COLORS.get(v, "#444"), marker="o", markersize=5,
                        linewidth=2, label=v)
        style(ax, title, "points n", ylabel)
    axs[0].legend(frameon=False, fontsize=8)
    fig.tight_layout()
    fig.savefig(out.parent / "slotread.png")


def main() -> None:
    if len(sys.argv) < 2 or sys.argv[1] not in ("run", "plot"):
        raise SystemExit(__doc__)
    out, args = out_and_args("slotread", sys.argv[2:])
    if sys.argv[1] == "plot":
        return plot(out)
    variants = next((a.split("=", 1)[1].split(",") for a in args if a.startswith("variants=")),
                    VARIANTS)
    ns = [int(a) for a in args if a.isdigit()] or NS
    run(out, ns, variants)


if __name__ == "__main__":
    main()
