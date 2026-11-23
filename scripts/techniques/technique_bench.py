# Copyright (c) 2026 Nicola Falciola. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Nicola Falciola
"""Shared harness of the technique benchmarks (results in `docs/techniques/<t>/`): synthetic Lean
files that import nothing (core Lean only), each metered in full and without the kernel. Copied
from ModularSymbolsTau (`scripts/bench/technique_bench.py`), on the meter of `scripts/meter.py`.

`measure(src)` writes `src` to a temporary file and runs it under `/usr/bin/time -l` twice, in full
and with `-Ddebug.skipKernelTC=true`, against a baseline (an empty file, metered once per process):

* `kernel_G`, `kernel_s`: full − no-kernel, instructions (billions) and wall seconds;
* `elab_G`, `elab_s`: no-kernel − baseline (parsing, elaboration, compilation);
* `peak_GB`, `peak_nokernel_GB`: peak memory footprint of the two runs.

A run killed by the watchdog of `meter.watched` (`MEM_LIMIT_GB`, `TIME_LIMIT_S`), or a file that
fails, raises `RuntimeError`; when only the full run fails, the message starts with `kernel:`.
These files run with `lean`'s defaults, not the options of `meter.OPTS`, as in the source.

`out_and_args(t, argv)` reads the arguments `[OUT.jsonl] …` of a bench: `OUT` defaults to
`docs/techniques/<t>/results.jsonl`. `append(out, row)` adds a JSON row; `done(out)` the keys
already there, so a sweep resumes.
"""

from __future__ import annotations

import json
import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from meter import REPO, SKIP, Limit, lean_env, rusage, watched  # noqa: E402

_BASE: dict | None = None


def run_lean(file: Path, opts: list[str] = ()) -> dict:
    lean, env = lean_env()
    try:
        rc, out, err = watched(["/usr/bin/time", "-l", lean, *opts, str(file)], env)
    except Limit as e:
        raise RuntimeError(f"{file}: {e}") from e
    if rc != 0 or out.strip():
        raise RuntimeError(f"{file}: lean failed ({rc}):\n{out[:3000]}\n{err[-3000:]}")
    return rusage(err)


def _run(src: str, opts: list[str] = ()) -> dict:
    with tempfile.TemporaryDirectory() as tmp:
        f = Path(tmp) / "Bench.lean"
        f.write_text(src)
        return run_lean(f, opts)


def measure(src: str) -> dict:
    global _BASE
    if _BASE is None:
        _BASE = _run("/-! Baseline: an empty file. -/\n", SKIP)
    skip = _run(src, SKIP)
    try:
        full = _run(src)
    except RuntimeError as e:
        raise RuntimeError(f"kernel: {e} (without the kernel: {skip['instr']:.1f} G, "
                           f"{skip['real']:.1f} s)") from e
    return {"kernel_G": round(full["instr"] - skip["instr"], 4),
            "kernel_s": round(full["real"] - skip["real"], 3),
            "elab_G": round(skip["instr"] - _BASE["instr"], 4),
            "elab_s": round(skip["real"] - _BASE["real"], 3),
            "peak_GB": round(full["peak"], 3), "peak_nokernel_GB": round(skip["peak"], 3),
            "src_bytes": len(src.encode())}


def out_and_args(technique: str, argv: list[str]) -> tuple[Path, list[str]]:
    """`OUT` (the first argument if it ends in `.jsonl`, else `docs/techniques/<t>/results.jsonl`)
    and the arguments after it."""
    if argv and argv[0].endswith(".jsonl"):
        return Path(argv[0]), argv[1:]
    return REPO / "docs" / "techniques" / technique / "results.jsonl", argv


def done(out: Path, *keys: str) -> set[tuple]:
    if not out.exists():
        return set()
    return {tuple(r[k] for k in keys) for r in map(json.loads, out.read_text().splitlines())}


def append(out: Path, row: dict) -> None:
    out.parent.mkdir(parents=True, exist_ok=True)
    print(json.dumps(row), flush=True)
    with out.open("a") as fh:
        fh.write(json.dumps(row) + "\n")


def load(out: Path) -> list[dict]:
    return [json.loads(ln) for ln in out.read_text().splitlines()]


def write_csv(rows: list[dict], path: Path) -> None:
    import csv
    keys = list(dict.fromkeys(k for r in rows for k in r))
    with path.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=keys)
        w.writeheader()
        w.writerows(rows)


def style(ax, title: str, xlabel: str, ylabel: str) -> None:
    ax.set_xscale("log", base=2)
    ax.set_yscale("log")
    ax.set_title(title, loc="left", fontsize=11)
    ax.set_xlabel(xlabel)
    ax.set_ylabel(ylabel)
    ax.grid(True, which="major", color="#e4e3dd", linewidth=0.6)
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)
