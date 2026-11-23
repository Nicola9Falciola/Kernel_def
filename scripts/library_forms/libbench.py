#!/usr/bin/env python3
# Copyright (c) 2026 Nicola Falciola. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Nicola Falciola
"""Library functions in the kernel against their kernel forms (`docs/library_forms/README.md`).

Each file holds the kernel forms of the library (`KernelDef/ListForms.lean`, `NatForms.lean`,
`IntForms.lean`, `MathlibForms.lean`) as the terms the compiler generated, the data of one
candidate, and one `decide +kernel` check that consumes the result. The variants of a candidate
differ only in the expression checked:

* `lib`  — what the compiler emits without the rule: the library call, its arguments compiled;
* `kf`   — what it emits with the rule: the kernel form;
* other `kf_…` and `lib_…` — variants (a generic form, a fusion, another way to write the call);
* `base` — the data alone (`Nat.beq 0 0`), subtracted; `consumer` — the walk that consumes a list
  result (`listSumNat`), subtracted for the candidates that return a list.

The files import nothing (core only), except those of `factorial`, `fib`, `digits`, `prime` and
`primeBig`, which import the Mathlib modules that define them, against a baseline with the same
imports. They are metered by the harness of the technique benchmarks
(`scripts/techniques/technique_bench.py`: a full run and one with `-Ddebug.skipKernelTC=true`, the
kernel's work the difference); heartbeats are read around the check with `IO.getNumHeartbeats`
(`Elab.async false`), in both runs.

The terms come from `export`, which runs `scripts/library_forms/Export.lean` (it imports the
built library: `lake build` first) and writes them to `$KERNEL_DEF_WORK/library_forms/`.

    python3 scripts/library_forms/libbench.py export
    python3 scripts/library_forms/libbench.py run [OUT.jsonl] [CANDIDATE|GROUP …]
    python3 scripts/library_forms/libbench.py list
    python3 scripts/library_forms/libbench.py src CANDIDATE VARIANT SIZE

`OUT` defaults to `docs/library_forms/results.jsonl`; a sweep resumes where it stopped. Every run
is heavy: one at a time on the machine, and cap it with `TIME_LIMIT_S` and `MEM_LIMIT_GB` (the
library forms of `Array.foldl`, `Nat.all`, `decide (∀ i < n, …)` and `decide (Nat.Prime p)` reach
24 GB at the largest sizes).
"""

from __future__ import annotations

import json
import random
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "techniques"))
import technique_bench as tb  # noqa: E402
from meter import REPO, WORK, lean_env  # noqa: E402

HERE = Path(__file__).resolve().parent
OUT_DIR = WORK / "library_forms"
EXPORT = OUT_DIR / "forms_export.txt"
HB = OUT_DIR / "hb"
SIZES = [256, 1024, 4096, 16384]


def export() -> None:
    """The terms of the kernel forms, by `Export.lean`, into `EXPORT`."""
    OUT_DIR.mkdir(parents=True, exist_ok=True)
    lean, env = lean_env()
    env = dict(env, LIBFORMS_EXPORT=str(EXPORT))
    proc = subprocess.run([lean, str(HERE / "Export.lean")], cwd=REPO, env=env,
                          capture_output=True, text=True)
    if proc.returncode != 0 or not EXPORT.exists():
        raise SystemExit(f"Export.lean failed:\n{proc.stdout}\n{proc.stderr}")
    print("terms written to", EXPORT)


def prelude() -> str:
    """The kernel forms, as `noncomputable def`s with the generated terms."""
    if not EXPORT.exists():
        export()
    out = []
    for block in EXPORT.read_text().split("### ")[1:]:
        head, ty, *val = block.rstrip("\n").split("\n")
        out.append(f"noncomputable def {head} : {ty} :=\n" + "\n".join(val))
    return "\n\n".join(out)


HEADER = """set_option linter.unusedVariables false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false
"""

MATHLIB_IMPORTS = """import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Defs
"""


def nat_list(vals: list[int]) -> str:
    return "[" + ", ".join(f"nat_lit {v}" for v in vals) + "]"


def int_lit(v: int) -> str:
    return f"Int.ofNat (nat_lit {v})" if v >= 0 else f"Int.negSucc (nat_lit {-v - 1})"


def rand_vals(m: int, bound: int = 1 << 16, seed: int = 1) -> list[int]:
    rng = random.Random(seed * 1000003 + m)
    return [rng.randrange(bound) for _ in range(m)]


SUMN = "KernelDef.listSumNat"
GETD = "KernelDef.listGetD"
ORECN = "@Option.rec Nat (fun _ => Nat) (nat_lit 0) (fun a => a)"


def loop(step: str, data: str = "xs", elem: str = "Nat", acc0: str = "nat_lit 0",
         acc: str = "Nat") -> str:
    """A bare `List.rec` over `data` whose step is `step` (in `x` and `ih`)."""
    return f"@List.rec ({elem}) (fun _ => {acc}) ({acc0}) (fun x _ ih => {step}) {data}"


class Cand:
    """A candidate: its data at size `m`, its variants (expressions) and the expected value."""

    def __init__(self, name, group, data, variants, expect, sizes=SIZES, kind="nat",
                 list_out=None, mathlib=False, note=""):
        self.name, self.group, self.data, self.variants = name, group, data, variants
        self.expect, self.sizes, self.kind, self.list_out = expect, sizes, kind, list_out
        self.mathlib, self.note = mathlib, note


def d_xs(m):
    xs = rand_vals(m)
    return f"noncomputable def xs : List Nat := {nat_list(xs)}\n", {"xs": xs}


def d_xs_target(m):
    """`xs` whose last element `2^17` occurs once: a search walks the whole list."""
    xs = rand_vals(m)
    xs[-1] = 1 << 17
    return f"noncomputable def xs : List Nat := {nat_list(xs)}\n", {"xs": xs}


def d_xs_ys(m):
    xs, ys = rand_vals(m), rand_vals(m, seed=2)
    return (f"noncomputable def xs : List Nat := {nat_list(xs)}\n"
            f"noncomputable def ys : List Nat := {nat_list(ys)}\n"), {"xs": xs, "ys": ys}


def d_xs_xs2(m):
    xs = rand_vals(m)
    return (f"noncomputable def xs : List Nat := {nat_list(xs)}\n"
            f"noncomputable def xs2 : List Nat := {nat_list(xs)}\n"), {"xs": xs}


def d_xss(m):
    xs = rand_vals(m)
    chunks = [xs[i:i + 4] for i in range(0, m, 4)]
    body = "[" + ", ".join(nat_list(c) for c in chunks) + "]"
    return f"noncomputable def xss : List (List Nat) := {body}\n", {"xs": xs}


def d_ps(m):
    vs = rand_vals(m)
    ks = list(range(m))
    body = "[" + ", ".join(f"(nat_lit {k}, nat_lit {v})" for k, v in zip(ks, vs)) + "]"
    return f"noncomputable def ps : List (Nat × Nat) := {body}\n", {"vs": vs}


def d_opts(m):
    vs = rand_vals(m)
    rng = random.Random(m)
    os_ = [v if rng.random() < 0.5 else None for v in vs]
    body = "[" + ", ".join("none" if o is None else f"some (nat_lit {o})" for o in os_) + "]"
    return f"noncomputable def os : List (Option Nat) := {body}\n", {"os": os_}


def d_bools(m):
    rng = random.Random(m)
    bs = [rng.random() < 0.5 for _ in range(m)]
    body = "[" + ", ".join("true" if b else "false" for b in bs) + "]"
    return f"noncomputable def bs : List Bool := {body}\n", {"bs": bs}


def d_ints(m):
    rng = random.Random(m)
    zs = [rng.randrange(-(1 << 15), 1 << 15) for _ in range(m)]
    body = "[" + ", ".join(int_lit(z) for z in zs) + "]"
    return f"noncomputable def zs : List Int := {body}\n", {"zs": zs}


def d_arr(m):
    xs = rand_vals(m)
    return (f"noncomputable def xs : List Nat := {nat_list(xs)}\n"
            f"noncomputable def arr : Array Nat := List.toArray xs\n"), {"xs": xs}


def d_none(m):
    return "", {}


def d_big(bits):
    """256 values of `bits` bits each."""
    def mk(m):
        rng = random.Random(bits)
        xs = [rng.randrange(1 << (bits - 1), 1 << bits) for _ in range(256)]
        return f"noncomputable def xs : List Nat := {nat_list(xs)}\n", {"xs": xs}
    return mk


def isqrt(n):
    import math
    return math.isqrt(n)


def tdiv(a, b):  # Lean's Int `/` (Euclidean, b > 0)
    return a // b if b > 0 else -(a // -b)


C = 32768
CANDS: list[Cand] = []


def add(*a, **k):
    CANDS.append(Cand(*a, **k))


# Lists -------------------------------------------------------------------------------------------
add("length", "list", d_xs,
    {"lib": "List.length xs",
     "kf": "@List.rec Nat (fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.add ih (nat_lit 1)) xs"},
    lambda d, m: m, note="control: `listLength`, a rule since the port")
add("foldl", "list", d_xs,
    {"lib": "@List.foldl Nat Nat (fun a x => Nat.add a x) (nat_lit 0) xs",
     "kf": "@KernelDef.listFoldl Nat Nat (fun a x => Nat.add a x) (nat_lit 0) xs"},
    lambda d, m: sum(d["xs"]))
add("sum", "list", d_xs,
    {"lib": "List.sum xs", "kf": f"{SUMN} xs", "kf_generic": "KernelDef.listSum xs"},
    lambda d, m: sum(d["xs"]))
add("mapsum", "list", d_xs,
    {"lib": "List.sum (@List.rec Nat (fun _ => List Nat) [] (fun a _ ih => Nat.mul (nat_lit 2) a :: ih) xs)",
     "kf": f"{SUMN} (@List.rec Nat (fun _ => List Nat) [] (fun a _ ih => Nat.mul (nat_lit 2) a :: ih) xs)",
     "kf_fused": "@List.rec Nat (fun _ => Nat) (nat_lit 0) (fun a _ ih => Nat.add (Nat.mul (nat_lit 2) a) ih) xs"},
    lambda d, m: 2 * sum(d["xs"]), note="`(l.map f).sum`; `kf_fused` is a fusion, not a rule")
add("reverse", "list", d_xs,
    {"lib": f"{SUMN} (List.reverse xs)", "kf": f"{SUMN} (@KernelDef.listReverseAux Nat xs [])"},
    lambda d, m: sum(d["xs"]), list_out=lambda m: m)
add("take", "list", d_xs,
    {"lib": "{s} (List.take (nat_lit {k}) xs)", "kf": "{s} (@KernelDef.listTake Nat (nat_lit {k}) xs)"},
    lambda d, m: sum(d["xs"][:m - 1]), list_out=lambda m: m - 1)
add("drop", "list", d_xs,
    {"lib": "{s} (List.drop (nat_lit {k}) xs)", "kf": "{s} (@KernelDef.listDrop Nat (nat_lit {k}) xs)"},
    lambda d, m: d["xs"][-1], list_out=lambda m: 1)
add("zipWith", "list", d_xs_ys,
    {"lib": f"{SUMN} (List.zipWith (fun a b => Nat.add a b) xs ys)",
     "kf": f"{SUMN} (@KernelDef.listZipWith Nat Nat Nat (fun a b => Nat.add a b) xs ys)"},
    lambda d, m: sum(d["xs"]) + sum(d["ys"]), list_out=lambda m: m)
add("getElem?", "list", d_xs,
    {"lib": f"{ORECN} (xs[(nat_lit {{k}})]?)", "kf": f"{ORECN} (@KernelDef.listGet? Nat xs (nat_lit {{k}}))"},
    lambda d, m: d["xs"][m - 1], note="`l[i]?` at the last index")
add("getElem?getD", "list", d_xs,
    {"lib": "Option.getD (xs[(nat_lit {k})]?) (nat_lit 0)", "kf": f"@{GETD} Nat xs (nat_lit {{k}}) (nat_lit 0)"},
    lambda d, m: d["xs"][m - 1], note="`l[i]?.getD d` at the last index")
add("getElem!", "list", d_xs,
    {"lib": "xs[(nat_lit {k})]!", "kf": f"@{GETD} Nat xs (nat_lit {{k}}) (@Inhabited.default Nat instInhabitedNat)"},
    lambda d, m: d["xs"][m - 1], note="`l[i]!` at the last index")
add("find?", "list", d_xs_target,
    {"lib": f"{ORECN} (List.find? (fun x => Nat.beq x (nat_lit {1 << 17})) xs)",
     "kf": f"{ORECN} (@KernelDef.listFind? Nat (fun x => Nat.beq x (nat_lit {1 << 17})) xs)"},
    lambda d, m: 1 << 17)
add("elem", "list", d_xs_target,
    {"lib": f"List.elem (nat_lit {1 << 17}) xs", "kf": f"KernelDef.listElemNat (nat_lit {1 << 17}) xs",
     "kf_generic": f"KernelDef.listElem (nat_lit {1 << 17}) xs"},
    lambda d, m: True, kind="bool", note="also `contains` and `decide (a ∈ l)`")
add("count", "list", d_xs_target,
    {"lib": f"List.count (nat_lit {1 << 17}) xs", "kf": f"KernelDef.listCountNat (nat_lit {1 << 17}) xs"},
    lambda d, m: 1)
add("flatten", "list", d_xss,
    {"lib": f"{SUMN} (List.flatten xss)", "kf": f"{SUMN} (@KernelDef.listFlatten Nat xss)"},
    lambda d, m: sum(d["xs"]), list_out=lambda m: m, note="m/4 lists of 4")
add("flatMap", "list", d_xs,
    {"lib": f"{SUMN} (List.flatMap (fun x => [x, x]) xs)",
     "kf": f"{SUMN} (@KernelDef.listFlatMap Nat Nat (fun x => [x, x]) xs)"},
    lambda d, m: 2 * sum(d["xs"]), list_out=lambda m: 2 * m)
add("lookup", "list", d_ps,
    {"lib": f"{ORECN} (List.lookup (nat_lit {{k}}) ps)", "kf": f"{ORECN} (@KernelDef.listLookupNat Nat (nat_lit {{k}}) ps)"},
    lambda d, m: d["vs"][m - 1], note="key at the end; a list of pairs")
add("max?", "list", d_xs,
    {"lib": f"{ORECN} (List.max? xs)", "kf": f"{ORECN} (KernelDef.listMaxNat? xs)"},
    lambda d, m: max(d["xs"]))
add("listEq", "list", d_xs_xs2,
    {"lib": "decide (xs = xs2)", "lib_beq": "xs == xs2", "kf": "KernelDef.listBEqNat xs xs2"},
    lambda d, m: True, kind="bool", note="`decide (l = r)` and `l == r` on `List ℕ`")
add("arrayFoldl", "list", d_arr,
    {"lib": "Array.foldl (fun a x => Nat.add a x) (nat_lit 0) arr",
     "kf": "@KernelDef.listFoldl Nat Nat (fun a x => Nat.add a x) (nat_lit 0) (Array.toList arr)"},
    lambda d, m: sum(d["xs"]))
add("arrayGet!", "list", d_arr,
    {"lib": "arr[(nat_lit {k})]!", "kf": f"@{GETD} Nat (Array.toList arr) (nat_lit {{k}}) (@Inhabited.default Nat instInhabitedNat)"},
    lambda d, m: d["xs"][m - 1])
add("arraySize", "list", d_arr,
    {"lib": "Array.size arr",
     "kf": "@List.rec Nat (fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.add ih (nat_lit 1)) (Array.toList arr)"},
    lambda d, m: m)
add("natAll", "list", d_none,
    {"lib": "Nat.all (nat_lit {m}) (fun i _ => Bool.rec true false (Nat.beq (Nat.mul i i) (nat_lit 7)))",
     "lib_decide": "decide (∀ i < (nat_lit {m}), Nat.mul i i ≠ nat_lit 7)",
     "kf": "KernelDef.natAll (nat_lit {m}) (fun i => Bool.rec true false (Nat.beq (Nat.mul i i) (nat_lit 7)))"},
    lambda d, m: True, kind="bool", note="`Nat.all n fun i _ ↦ …`; `lib_decide` is `decide (∀ i < n, …)`")

# Scalars, one use a step of a loop over `xs` ----------------------------------------------------
add("min", "scalar", d_xs,
    {"lib": loop(f"Nat.add ih (Min.min x (nat_lit {C}))"),
     "kf": loop(f"Nat.add ih (Bool.rec (nat_lit {C}) x (Nat.ble x (nat_lit {C})))")},
    lambda d, m: sum(min(x, C) for x in d["xs"]))
add("max", "scalar", d_xs,
    {"lib": loop(f"Nat.add ih (Max.max x (nat_lit {C}))"),
     "kf": loop(f"Nat.add ih (Bool.rec x (nat_lit {C}) (Nat.ble x (nat_lit {C})))")},
    lambda d, m: sum(max(x, C) for x in d["xs"]))
add("lt", "scalar", d_xs,
    {"lib": loop(f"Bool.rec ih (Nat.add ih (nat_lit 1)) (Nat.blt x (nat_lit {C}))"),
     "kf": loop(f"Bool.rec ih (Nat.add ih (nat_lit 1)) (Nat.ble (Nat.succ x) (nat_lit {C}))"),
     "kf_add": loop(f"Bool.rec ih (Nat.add ih (nat_lit 1)) (Nat.ble (Nat.add x (nat_lit 1)) (nat_lit {C}))"),
     "kf_not": loop(f"Bool.rec (Nat.add ih (nat_lit 1)) ih (Nat.ble (nat_lit {C}) x)")},
    lambda d, m: sum(1 for x in d["xs"] if x < C),
    note="`a < b`: the compiler writes `Nat.blt` (lib); `kf_not` swaps the branches of `Nat.ble b a`")
add("testBit", "scalar", d_xs,
    {"lib": loop("Bool.rec ih (Nat.add ih (nat_lit 1)) (Nat.testBit x (nat_lit 3))"),
     "kf": loop("Bool.rec ih (Nat.add ih (nat_lit 1)) (KernelDef.natTestBit x (nat_lit 3))")},
    lambda d, m: sum(1 for x in d["xs"] if x >> 3 & 1))
add("lcm", "scalar", d_xs,
    {"lib": loop("Nat.add ih (Nat.lcm x (nat_lit 12))"),
     "kf": loop("Nat.add ih (Nat.div (Nat.mul x (nat_lit 12)) (Nat.gcd x (nat_lit 12)))")},
    lambda d, m: sum(x * 12 // __import__("math").gcd(x, 12) if x else 0 for x in d["xs"]))
add("pred", "scalar", d_xs,
    {"lib": loop("Nat.add ih (Nat.pred x)"), "kf": loop("Nat.add ih (Nat.sub x (nat_lit 1))")},
    lambda d, m: sum(max(x - 1, 0) for x in d["xs"]))
add("optGetD", "scalar", d_opts,
    {"lib": loop("Nat.add ih (Option.getD x (nat_lit 0))", data="os", elem="Option Nat"),
     "kf": loop("Nat.add ih (@Option.rec Nat (fun _ => Nat) (nat_lit 0) (fun a => a) x)", data="os",
                elem="Option Nat")},
    lambda d, m: sum(o or 0 for o in d["os"]))
add("boolEq", "scalar", d_bools,
    {"lib": loop("Bool.rec ih (Nat.add ih (nat_lit 1)) (x == false)", data="bs", elem="Bool"),
     "kf": loop("Bool.rec ih (Nat.add ih (nat_lit 1)) (@Bool.rec (fun _ => Bool) (Bool.rec true false false) false x)",
                data="bs", elem="Bool")},
    lambda d, m: sum(1 for b in d["bs"] if not b), note="`a == b`, `a != b`, `xor` on `Bool`")

# Int, one use a step -----------------------------------------------------------------------------
I0 = "Int.ofNat (nat_lit 0)"


def int_check(step):
    return loop(step, data="zs", elem="Int", acc0=I0, acc="Int")


def nat_over_ints(step):
    return loop(step, data="zs", elem="Int")


M3 = "(Int.negSucc (nat_lit 2))"
SEVEN = "(Int.ofNat (nat_lit 7))"
HUNDRED = "(Int.ofNat (nat_lit 100))"
add("intAdd", "int", d_ints, {"lib": int_check("ih + x"), "kf": int_check("Int.add_k ih x")},
    lambda d, m: sum(d["zs"]), kind="int")
add("intMul", "int", d_ints,
    {"lib": int_check(f"Int.add_k ih (x * {M3})"), "kf": int_check(f"Int.add_k ih (Int.mul_k x {M3})")},
    lambda d, m: sum(-3 * z for z in d["zs"]), kind="int")
add("intSub", "int", d_ints, {"lib": int_check("ih - x"), "kf": int_check("Int.sub_k ih x")},
    lambda d, m: -sum(d["zs"]), kind="int", note="right fold: `x₁ - (x₂ - …)` is not this; see expected")
add("intNeg", "int", d_ints,
    {"lib": int_check("Int.add_k ih (-x)"), "kf": int_check("Int.add_k ih (Int.neg_k x)")},
    lambda d, m: -sum(d["zs"]), kind="int")
add("intNatAbs", "int", d_ints,
    {"lib": nat_over_ints("Nat.add ih (Int.natAbs x)"), "kf": nat_over_ints("Nat.add ih (Int.natAbs_k x)")},
    lambda d, m: sum(abs(z) for z in d["zs"]))
add("intEmod", "int", d_ints,
    {"lib": int_check(f"Int.add_k ih (x % {SEVEN})"), "kf": int_check(f"Int.add_k ih (Int.emod_k x {SEVEN})")},
    lambda d, m: sum(z % 7 for z in d["zs"]), kind="int")
add("intEdiv", "int", d_ints,
    {"lib": int_check(f"Int.add_k ih (x / {SEVEN})"), "kf": int_check(f"Int.add_k ih (Int.ediv_k x {SEVEN})")},
    lambda d, m: sum(z // 7 for z in d["zs"]), kind="int")
add("intLt", "int", d_ints,
    {"lib": nat_over_ints(f"Bool.rec ih (Nat.add ih (nat_lit 1)) (decide (x < {HUNDRED}))"),
     "kf": nat_over_ints(f"Bool.rec ih (Nat.add ih (nat_lit 1)) (Int.blt' x {HUNDRED})")},
    lambda d, m: sum(1 for z in d["zs"] if z < 100))
add("intEq", "int", d_ints,
    {"lib": nat_over_ints(f"Bool.rec ih (Nat.add ih (nat_lit 1)) (decide (x = {HUNDRED}))"),
     "kf": nat_over_ints(f"Bool.rec ih (Nat.add ih (nat_lit 1)) (KernelDef.intBEq x {HUNDRED})")},
    lambda d, m: sum(1 for z in d["zs"] if z == 100))
add("intLit", "int", d_ints,
    {"lib": int_check("Int.add_k ih (Int.add_k x (5 : Int))"),
     "kf": int_check("Int.add_k ih (Int.add_k x (Int.ofNat (nat_lit 5)))")},
    lambda d, m: sum(z + 5 for z in d["zs"]), kind="int", note="an `Int` numeral, `OfNat.ofNat` against `Int.ofNat`")

# Value-size functions ---------------------------------------------------------------------------
BITS = [32, 128, 512, 2048]
add("sqrt", "value", None,
    {"lib": loop("Nat.add ih (Nat.sqrt x)"), "kf": loop("Nat.add ih (KernelDef.natSqrt x)")},
    None, sizes=BITS, note="256 values of `size` bits; the kernel form's first guess through `natLog2`")
add("log2", "log2", None,
    {"lib": loop("Nat.add ih (Nat.log2 x)"), "kf": loop("Nat.add ih (KernelDef.natLog2 x)")},
    None, sizes=[64, 512, 2048], note="256 values of `size` bits; `Nat.log2` is no kernel primitive in "
    "v4.37.0-rc1: its `Nat.rec` takes one step a bit")
FACT = [256, 1024, 4096, 16384]
add("factorial", "value", d_none,
    {"lib": "Nat.factorial (nat_lit {m})", "kf": "KernelDef.natFactorial (nat_lit {m})"},
    None, sizes=FACT, mathlib=True, note="Mathlib")
add("fib", "value", d_none,
    {"lib": "Nat.fib (nat_lit {m})", "kf": "KernelDef.natFibAux (nat_lit {m}) (nat_lit 0) (nat_lit 1)"},
    None, sizes=[256, 1024, 4096, 16384, 65536], mathlib=True, note="Mathlib")
DIG = [64, 256, 1024, 4096, 16384]
add("digits", "value", d_none,
    {"lib": f"{SUMN} (Nat.digits 10 N)", "kf": f"{SUMN} (KernelDef.natDigits (nat_lit 10) N)"},
    None, sizes=DIG, mathlib=True, note="Mathlib; `N` has `size` decimal digits")
PRIMES = {256: 251, 1024: 1021, 4096: 4093, 16384: 16381, 65536: 65521, 1 << 20: 1048573,
          1 << 24: 16777213, 1 << 28: 268435399}
add("prime", "value", d_none,
    {"lib": "decide (Nat.Prime (nat_lit {p}))", "kf": "KernelDef.natPrime (nat_lit {p})"},
    None, sizes=[256, 1024, 4096, 16384, 65536], kind="bool", mathlib=True,
    note="Mathlib; the largest prime below `size`")
add("primeBig", "primeBig", d_none, {"kf": "KernelDef.natPrime (nat_lit {p})"},
    None, sizes=[1 << 20, 1 << 24, 1 << 28], kind="bool", mathlib=True,
    note="the kernel form alone, beyond the reach of the library")


def expr_for(c: Cand, v: str, m: int) -> str:
    e = c.variants[v]
    return e.replace("{s}", SUMN).replace("{k}", str(m - 1)).replace("{m}", str(m)).replace(
        "{p}", str(PRIMES.get(m, 0)))


def data_for(c: Cand, m: int):
    if c.name in ("sqrt", "log2"):
        return d_big(m)(m)
    if c.name == "digits":
        rng = random.Random(m)
        n = int("".join([str(rng.randrange(1, 10))] + [str(rng.randrange(10)) for _ in range(m - 1)]))
        return f"noncomputable def N : Nat := nat_lit {n}\n", {"N": n}
    return c.data(m)


def expected(c: Cand, d: dict, m: int):
    if c.name == "sqrt":
        return sum(isqrt(x) for x in d["xs"])
    if c.name == "log2":
        return sum(x.bit_length() - 1 for x in d["xs"])
    if c.name == "factorial":
        import math
        return math.factorial(m)
    if c.name == "fib":
        a, b = 0, 1
        for _ in range(m):
            a, b = b, a + b
        return a
    if c.name == "digits":
        return sum(int(ch) for ch in str(d["N"]))
    if c.name in ("prime", "primeBig"):
        return True
    return c.expect(d, m)


def check(c: Cand, expr: str, val, kind: str) -> str:
    if kind == "bool":
        return f"({expr}) = {'true' if val else 'false'}"
    if kind == "int":
        return f"KernelDef.intBEq ({expr}) ({int_lit(val)}) = true"
    return f"Nat.beq ({expr}) (nat_lit {val}) = true"


def source(c: Cand, v: str, m: int, hbfile: Path) -> str:
    data, d = data_for(c, m)
    if v == "base":
        stmt = "Nat.beq (nat_lit 0) (nat_lit 0) = true"
    elif v == "consumer":
        stmt = f"Nat.beq ({SUMN} xs) (nat_lit {sum(d['xs'])}) = true"
    else:
        stmt = check(c, expr_for(c, v, m), expected(c, d, m), c.kind)
    rd = f'let h ← IO.FS.readFile "{hbfile}"; '
    hb = (f'#eval show IO Unit from do {rd}IO.FS.writeFile "{hbfile}" '
          f'(h ++ toString (← IO.getNumHeartbeats) ++ "\\n")')
    imports = MATHLIB_IMPORTS if c.mathlib else ""
    return (f"{imports}/-! libforms benchmark: `{c.name}`, variant `{v}`, size {m}. -/\n{HEADER}\n"
            f"{prelude()}\n\n{data}\n{hb}\n"
            f"theorem check : {stmt} := by decide +kernel\n{hb}\n")


_BASES: dict[bool, dict] = {}


def measure(src: str, mathlib: bool) -> dict:
    """`technique_bench.measure`, with a baseline that has the same imports."""
    if mathlib not in _BASES:
        _BASES[mathlib] = tb._run((MATHLIB_IMPORTS if mathlib else "") + "/-! Baseline. -/\n",
                                  tb.SKIP)
    base = _BASES[mathlib]
    skip = tb._run(src, tb.SKIP)
    try:
        full = tb._run(src)
    except RuntimeError as e:
        raise RuntimeError(f"kernel: {e} (without the kernel: {skip['instr']:.1f} G, "
                           f"{skip['real']:.1f} s)") from e
    return {"kernel_G": round(full["instr"] - skip["instr"], 4),
            "kernel_s": round(full["real"] - skip["real"], 3),
            "elab_G": round(skip["instr"] - base["instr"], 4),
            "elab_s": round(skip["real"] - base["real"], 3),
            "peak_GB": round(full["peak"], 3), "peak_nokernel_GB": round(skip["peak"], 3),
            "src_bytes": len(src.encode())}


def variants_of(c: Cand) -> list[str]:
    extra = ["base"]
    if c.list_out is not None:
        extra.append("consumer")
    return extra + list(c.variants)


def run(out: Path, names: list[str]) -> None:
    HB.mkdir(exist_ok=True)
    have = tb.done(out, "cand", "variant", "size")
    for c in CANDS:
        if names and c.name not in names and c.group not in names:
            continue
        for m in c.sizes:
            for v in variants_of(c):
                if (c.name, v, m) in have:
                    continue
                hbfile = HB / f"{c.name}_{v}_{m}.txt".replace("?", "Q").replace("!", "B")
                hbfile.write_text("0\n")
                row = {"cand": c.name, "group": c.group, "variant": v, "size": m}
                try:
                    row |= measure(source(c, v, m, hbfile), c.mathlib)
                    h = [int(x) for x in hbfile.read_text().split()][1:]
                    if len(h) == 4:
                        row["hb_elab_k"] = round((h[1] - h[0]) / 1e3, 1)
                        row["hb_full_k"] = round((h[3] - h[2]) / 1e3, 1)
                        row["hb_kernel_k"] = round(row["hb_full_k"] - row["hb_elab_k"], 1)
                except RuntimeError as e:
                    msg = str(e)
                    row["error"] = (msg.splitlines()[0] if msg.startswith("kernel:") else
                                    next((ln for ln in msg.splitlines() if "error" in ln), msg))[:400]
                tb.append(out, row)


def main() -> None:
    cmd, args = (sys.argv[1], sys.argv[2:]) if len(sys.argv) > 1 else ("", [])
    if cmd == "export":
        export()
    elif cmd == "run":
        out, names = tb.out_and_args("", args)
        if not (args and args[0].endswith(".jsonl")):
            out = REPO / "docs" / "library_forms" / "results.jsonl"
        run(out, names)
    elif cmd == "list":
        for c in CANDS:
            print(f"{c.name:14s} {c.group:8s} {variants_of(c)} {c.sizes}")
    elif cmd == "src" and len(args) == 3:
        c = next(c for c in CANDS if c.name == args[0])
        print(source(c, args[1], int(args[2]), HB / "src.txt"))
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
