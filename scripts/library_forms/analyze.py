#!/usr/bin/env python3
# Copyright (c) 2026 Nicola Falciola. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Nicola Falciola
"""Tables of `results.jsonl` (libbench.py): the kernel cost of each variant net of the data
(`base`) and, for a list result, of the walk that consumes it (`consumer`, scaled to the length of
the result); per element (or per call for the group `value`), and the ratio library / kernel form.

    python3 scripts/library_forms/analyze.py [docs/library_forms/results.jsonl]

prints the tables (markdown) on stdout; `docs/library_forms/tables.txt` is its output.
"""

from __future__ import annotations

import json
import sys
from collections import defaultdict
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import libbench as lb  # noqa: E402

CAND = {c.name: c for c in lb.CANDS}


def per_unit(c, m):
    """What one unit is: an element of the list, or one call (`value`: one call; `sqrt`: 256)."""
    if c.name in ("sqrt", "log2"):
        return 256
    if c.group in ("value", "primeBig"):
        return 1
    return m


def nets(rows):
    by = defaultdict(dict)
    for r in rows:
        by[(r["cand"], r["size"])][r["variant"]] = r
    out = {}
    for (name, m), vs in by.items():
        c = CAND[name]
        b = vs.get("base")
        if b is None or "error" in b:
            continue
        cons = vs.get("consumer")
        cb = b
        if (cons is None or "error" in cons) and c.list_out:
            # `flatten` has no flat `xs` to consume: the walk of `reverse` at the same size, over
            # the same values, is the same consumer (net of the base of `reverse`)
            cons = by.get(("reverse", m), {}).get("consumer")
            cb = by.get(("reverse", m), {}).get("base", b)
        frac = c.list_out(m) / m if c.list_out else 0.0
        for v, r in vs.items():
            if v in ("base", "consumer"):
                continue
            if "error" in r:
                out[(name, m, v)] = {"error": r["error"]}
                continue
            g = r["kernel_G"] - b["kernel_G"]
            hb = r.get("hb_kernel_k", 0) - b.get("hb_kernel_k", 0)
            if frac and cons and "error" not in cons:
                g -= frac * (cons["kernel_G"] - cb["kernel_G"])
                hb -= frac * (cons.get("hb_kernel_k", 0) - cb.get("hb_kernel_k", 0))
            u = per_unit(c, m)
            out[(name, m, v)] = {"net_G": g, "per_unit_k": g * 1e6 / u, "kernel_G": r["kernel_G"],
                                 "kernel_s": r["kernel_s"], "peak_GB": r["peak_GB"],
                                 "hb_net_k": hb, "elab_G": r["elab_G"], "base_G": b["kernel_G"]}
    return out


def fmt(x, nd=2):
    return f"{x:,.{nd}f}"


def main():
    src = Path(sys.argv[1]) if len(sys.argv) > 1 else (
        Path(__file__).resolve().parents[2] / "docs" / "library_forms" / "results.jsonl")
    rows = [json.loads(ln) for ln in src.read_text().splitlines()]
    N = nets(rows)
    names = [c.name for c in lb.CANDS if any(k[0] == c.name for k in N)]

    def variants(name):
        """The variants of `name` in the rows: those of the harness first, then any other (an
        older harness's, such as `kf_fastlog2` of `sqrt` in the rows of 2026-11-22)."""
        seen = list(dict.fromkeys(k[2] for k in N if k[0] == name))
        return [v for v in CAND[name].variants if v in seen] + \
            [v for v in seen if v not in CAND[name].variants]
    print("| function | size | variant | kernel G (raw) | net G | per unit (k instr) | "
          "lib / variant | net heartbeats (k) | peak GB | kernel s |")
    print("|---|---:|---|---:|---:|---:|---:|---:|---:|---:|")
    for name in names:
        c = CAND[name]
        for m in c.sizes:
            lib = N.get((name, m, "lib"))
            for v in variants(name):
                r = N.get((name, m, v))
                if r is None:
                    continue
                if "error" in r:
                    print(f"| {name} | {m} | {v} | error: {r['error'][:80]} | | | | | | |")
                    continue
                ratio = (lib["net_G"] / r["net_G"]) if lib and "error" not in lib and r["net_G"] > 0 \
                    else float("nan")
                print(f"| {name} | {m} | {v} | {fmt(r['kernel_G'], 3)} | {fmt(r['net_G'], 3)} | "
                      f"{fmt(r['per_unit_k'], 1)} | {fmt(ratio, 2)} | {fmt(r['hb_net_k'], 0)} | "
                      f"{fmt(r['peak_GB'], 3)} | {fmt(r['kernel_s'], 3)} |")
    # summary at the largest size measured with both variants
    print("\n## Summary at the largest size\n")
    print("| function | group | size | lib per unit (k) | kf per unit (k) | saved per unit (k) | ratio | "
          "lib net G | kf net G | lib / kf heartbeats (k) | other variants (ratio lib / v) |")
    print("|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|")
    summ = []
    for name in names:
        c = CAND[name]
        for m in reversed(c.sizes):
            lib, kf = N.get((name, m, "lib")), N.get((name, m, "kf"))
            if lib and kf and "error" not in kf:
                others = []
                for v in variants(name):
                    if v in ("lib", "kf"):
                        continue
                    r = N.get((name, m, v))
                    if r and "error" not in r and "error" not in lib and r["net_G"] > 0:
                        others.append(f"{v}: {lib['net_G'] / r['net_G']:.2f}")
                    elif r and "error" in r:
                        others.append(f"{v}: error")
                if "error" in lib:
                    summ.append((float("inf"), name, c.group, m, None, kf, others))
                else:
                    ratio = lib["net_G"] / kf["net_G"] if kf["net_G"] > 0 else float("inf")
                    summ.append((ratio, name, c.group, m, lib, kf, others))
                break
    for ratio, name, g, m, lib, kf, others in sorted(summ, key=lambda t: -t[0]):
        ls = "error" if lib is None else fmt(lib["per_unit_k"], 1)
        lg = "error" if lib is None else fmt(lib["net_G"], 3)
        sv = "—" if lib is None else fmt(lib["per_unit_k"] - kf["per_unit_k"], 1)
        hb = "—" if lib is None else f"{lib['hb_net_k']:,.0f} / {kf['hb_net_k']:,.0f}"
        print(f"| {name} | {g} | {m} | {ls} | {fmt(kf['per_unit_k'], 1)} | {sv} | {fmt(ratio, 2)} | "
              f"{lg} | {fmt(kf['net_G'], 3)} | {hb} | {'; '.join(others)} |")


if __name__ == "__main__":
    main()
