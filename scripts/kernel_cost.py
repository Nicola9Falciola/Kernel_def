#!/usr/bin/env python3
# Copyright (c) 2026 Nicola Falciola. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Nicola Falciola
"""The kernel's cost of a Lean file, before and after a change of the compiler (the meter of
ModularSymbolsTau's `scripts/bench/kernel_form/level_cost.py`, `plain_ab.py` and `bench.py`).

    python3 scripts/kernel_cost.py run OUT.jsonl TAG FILE.lean [FILE.lean ...]
    python3 scripts/kernel_cost.py report OUT.jsonl TAG_A TAG_B
    python3 scripts/kernel_cost.py noise FILE.lean [RUNS]

`run`: each file, in place, `REPEATS` times (default 3) in full and `SKIP_REPEATS` times (default
`REPEATS`) with `-Ddebug.skipKernelTC=true`, single-threaded (`-j1`) with `-DElab.async=false`
(`meter.py`: the toolchain's `lean` with the project's search path, under `/usr/bin/time -l`);
the minimum of each is kept. One row a file, appended to `OUT`:

* `G`: instructions retired of the full run (billions), the least of the runs (`G_all`: all);
* `skip_G`: the same without the kernel; `kernel_G = G − skip_G`, the kernel's work;
* `real_s`, `skip_real_s`, `kernel_s`: the same in wall seconds;
* `peak_GB`: the peak memory footprint of the full run (`peak_all`: all);
* `tag`, `file`, `repeats`, `commit`, `compiler` (the hash of `KernelDef/KernelForm.lean`), `opts`.

A file imports the built `.olean`s: run `lake build` first, and after every change of the
compiler. `kernel_G` carries the noise of two runs: `noise FILE` runs a file `RUNS` times
(default 10) in full and prints the spread of `G`. `report` prints the files of `TAG_A` against
those of `TAG_B`. The files of `bench/` are made for this. Every run is heavy: one at a time on the
machine.
"""

from __future__ import annotations

import json
import os
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from meter import OPTS, REPO, SKIP, append, compiler_id, load, run_lean  # noqa: E402

REPEATS = int(os.environ.get("REPEATS", "3"))
SKIP_REPEATS = int(os.environ.get("SKIP_REPEATS", str(REPEATS)))


def meter(f: Path) -> dict:
    full = [run_lean(f) for _ in range(REPEATS)]
    if any("error" in r for r in full):
        r = next(r for r in full if "error" in r)
        return {"error": r["error"], **({"limit": True} if r.get("limit") else {})}
    skip = [run_lean(f, SKIP) for _ in range(SKIP_REPEATS)]
    if any("error" in r for r in skip):
        return {"error": "skip: " + next(r for r in skip if "error" in r)["error"]}
    out = {"G": round(min(r["instr"] for r in full), 4),
           "G_all": [round(r["instr"], 4) for r in full],
           "skip_G": round(min(r["instr"] for r in skip), 4),
           "skip_G_all": [round(r["instr"], 4) for r in skip],
           "real_s": round(min(r["real"] for r in full), 2),
           "skip_real_s": round(min(r["real"] for r in skip), 2),
           "peak_GB": round(min(r["peak"] for r in full), 3),
           "peak_all": [round(r["peak"], 3) for r in full]}
    out["kernel_G"] = round(out["G"] - out["skip_G"], 4)
    out["kernel_s"] = round(out["real_s"] - out["skip_real_s"], 2)
    return out


def rel(f: str) -> str:
    p = Path(f).resolve()
    return str(p.relative_to(REPO)) if p.is_relative_to(REPO) else str(p)


def run(out: Path, tag: str, files: list[str]) -> None:
    ident = compiler_id()
    for f in files:
        row = {"date": time.strftime("%Y-%m-%d %H:%M"), "tag": tag, "file": rel(f),
               "repeats": [REPEATS, SKIP_REPEATS], **ident, "opts": OPTS}
        append(out, row | meter(Path(f).resolve()))


def report(out: Path, a: str, b: str) -> None:
    rows = load(out)
    by = {(r["tag"], r["file"]): r for r in rows}
    files = list(dict.fromkeys(r["file"] for r in rows if r["tag"] in (a, b)))

    def cell(r: dict | None, k: str, fmt: str = "{:.3f}") -> str:
        if r is None:
            return ""
        return fmt.format(r[k]) if k in r else ("cap" if r.get("limit") else "error")
    print(f"| file | kernel G {a} | {b} | change | full G {a} | {b} | peak GB {a} | {b} | "
          f"wall s {a} | {b} |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|")
    for f in files:
        ra, rb = by.get((a, f)), by.get((b, f))
        ch = ""
        if ra and rb and "kernel_G" in ra and "kernel_G" in rb:
            d = rb["kernel_G"] - ra["kernel_G"]
            ch = f"{d:+.3f}" + (f" ({d / ra['kernel_G']:+.1%})" if ra["kernel_G"] > 0 else "")
        print(f"| {f} | {cell(ra, 'kernel_G')} | {cell(rb, 'kernel_G')} | {ch} | {cell(ra, 'G')} | "
              f"{cell(rb, 'G')} | {cell(ra, 'peak_GB')} | {cell(rb, 'peak_GB')} | "
              f"{cell(ra, 'real_s', '{:.2f}')} | {cell(rb, 'real_s', '{:.2f}')} |")


def noise(f: str, runs: int) -> None:
    rs = [run_lean(Path(f).resolve()) for _ in range(runs)]
    errs = [r for r in rs if "error" in r]
    if errs:
        raise SystemExit(errs[0]["error"])
    g = [round(r["instr"], 4) for r in rs]
    print(json.dumps({"file": rel(f), "runs": runs, "G_all": g, "G_min": min(g), "G_max": max(g),
                      "spread_G": round(max(g) - min(g), 4)}), flush=True)


def main() -> None:
    a = sys.argv[1:]
    if a[:1] == ["run"] and len(a) >= 4:
        run(Path(a[1]), a[2], a[3:])
    elif a[:1] == ["report"] and len(a) == 4:
        report(Path(a[1]), a[2], a[3])
    elif a[:1] == ["noise"] and len(a) in (2, 3):
        noise(a[1], int(a[2]) if len(a) == 3 else 10)
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
