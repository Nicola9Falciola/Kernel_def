# Copyright (c) 2026 Nicola Falciola. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Nicola Falciola
"""The meter shared by the scripts that measure Lean (`kernel_cost.py`, `heartbeats.py`,
`techniques/technique_bench.py`), taken from ModularSymbolsTau (`scripts/bench/meter.py`,
`scripts/bench/kernel_form/level_cost.py`, `plain_ab.py`).

The toolchain's `lean` binary is found once with `lake env which lean`, run from the repository
root, and its search path with `lake env printenv LEAN_PATH` (the packages and the repository's own
build: build first). `lean` is then run directly under `/usr/bin/time -l`, never through `lake`:
on macOS the counters of `/usr/bin/time -l` (instructions retired, cycles, peak memory footprint)
are those of the process it starts, so a run through `lake env lean` would count the wrapper only.

`run_lean` caps every run: `MEM_LIMIT_GB` (default 24, of a 32 GB machine), read every 0.3 s on
the process tree, and `TIME_LIMIT_S` (default 1800); a run past a cap is killed with its process
group and raises `Limit`. Its output goes to files: a pipe that fills up would leave `lean` asleep.
"""

from __future__ import annotations

import hashlib
import json
import os
import re
import subprocess
import tempfile
import time
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
# the options of `lakefile.toml` but its linters (`pp.unicode.fun` for the messages that a
# `#guard_msgs` expects); single-threaded, no asynchronous elaboration: the kernel's work is done
# in the run and counted
OPTS = ["-DmaxSynthPendingDepth=3", "-DrelaxedAutoImplicit=false", "-Dpp.unicode.fun=true",
        "-DElab.async=false", "-j1"]
SKIP = ["-Ddebug.skipKernelTC=true"]
MEM_LIMIT_GB = float(os.environ.get("MEM_LIMIT_GB", "24"))
TIME_LIMIT_S = float(os.environ.get("TIME_LIMIT_S", "1800"))
WORK = Path(os.environ.get("KERNEL_DEF_WORK", Path(tempfile.gettempdir()) / "kernel_def_work"))

_ENV: tuple[str, dict[str, str]] | None = None


class Limit(RuntimeError):
    pass


def lean_env() -> tuple[str, dict[str, str]]:
    """The `lean` binary of the project and the environment with its `LEAN_PATH`."""
    global _ENV
    if _ENV is None:
        def lake(*a: str) -> str:
            return subprocess.run(["lake", "env", *a], cwd=REPO, check=True, capture_output=True,
                                  text=True).stdout.strip()
        _ENV = (lake("which", "lean"), dict(os.environ, LEAN_PATH=lake("printenv", "LEAN_PATH")))
    return _ENV


def rusage(err: str) -> dict[str, float]:
    """The report of `/usr/bin/time -l` (macOS): seconds, billions of instructions and cycles,
    GB."""
    def num(pat: str) -> float:
        m = re.search(pat, err)
        return float(m.group(1)) if m else float("nan")
    return {"real": num(r"([\d.]+) real"), "user": num(r"([\d.]+) user"),
            "sys": num(r"([\d.]+) sys"), "instr": num(r"(\d+)\s+instructions retired") / 1e9,
            "cycles": num(r"(\d+)\s+cycles elapsed") / 1e9,
            "peak": num(r"(\d+)\s+peak memory footprint") / 1e9}


def mem_tree_gb(pid: int) -> float:
    """The resident memory of `pid` and its descendants, in GB."""
    ps = subprocess.run(["ps", "-A", "-o", "pid=,ppid=,rss="], capture_output=True, text=True)
    kids: dict[int, list[int]] = {}
    rss: dict[int, int] = {}
    for line in ps.stdout.splitlines():
        p, pp, r = map(int, line.split())
        kids.setdefault(pp, []).append(p)
        rss[p] = r
    tot, todo = 0, [pid]
    while todo:
        p = todo.pop()
        tot += rss.get(p, 0)
        todo += kids.get(p, [])
    return tot / 1e6


def watched(cmd: list[str], env: dict[str, str]) -> tuple[int, str, str]:
    """`cmd` from the repository root, killed with its process group past `TIME_LIMIT_S`, or when
    its memory, read every 0.3 s, would pass `MEM_LIMIT_GB` within a second at its last rate."""
    with tempfile.TemporaryFile("w+") as out, tempfile.TemporaryFile("w+") as err:
        proc = subprocess.Popen(cmd, stdout=out, stderr=err, text=True, start_new_session=True,
                                cwd=REPO, env=env)
        start, last, prev = time.monotonic(), 0.0, 0.0
        while proc.poll() is None:
            now = time.monotonic()
            if now - start > TIME_LIMIT_S:
                os.killpg(proc.pid, 9)
                proc.wait()
                raise Limit(f"time limit: killed after {TIME_LIMIT_S:.0f} s")
            if now - last >= 0.3:
                cur = mem_tree_gb(proc.pid)
                rate = max(0.0, (cur - prev) / (now - last)) if last else 0.0
                last, prev = now, cur
                if cur + rate > MEM_LIMIT_GB:
                    os.killpg(proc.pid, 9)
                    proc.wait()
                    raise Limit(f"memory limit: killed at {cur:.1f} GB after {now - start:.0f} s")
            time.sleep(0.05)
        out.seek(0)
        err.seek(0)
        return proc.returncode, out.read(), err.read()


def run_lean(file: Path, opts: list[str] = (), extra: list[str] = ()) -> dict:
    """One metered run of `lean` on `file`, with `OPTS` and `opts`: `rusage` and the output
    (`out`), or `error` when `lean` fails or prints an error; `limit` when a cap was hit."""
    lean, env = lean_env()
    try:
        rc, out, err = watched(["/usr/bin/time", "-l", lean, *OPTS, *opts, *extra, str(file)], env)
    except Limit as ex:
        return {"error": str(ex), "limit": True}
    if rc != 0 or re.search(r":\d+:\d+: error", out):
        return {"error": (out[:1500] or err[-600:]), "out": out}
    return {**rusage(err), "out": out}


def compiler_id() -> dict[str, str]:
    """What a row was measured with: the commit of the repository (with `+` if the working tree
    differs) and the hash of the compiler's source."""
    def git(*a: str) -> str:
        p = subprocess.run(["git", *a], cwd=REPO, capture_output=True, text=True)
        return p.stdout.strip() if p.returncode == 0 else ""
    head = git("rev-parse", "--short", "HEAD")
    dirty = "+" if git("status", "--porcelain", "--untracked-files=no") else ""
    src = (REPO / "KernelDef" / "KernelForm.lean").read_bytes()
    return {"commit": head + dirty, "compiler": hashlib.sha256(src).hexdigest()[:12]}


def append(out: Path, row: dict) -> None:
    out.parent.mkdir(parents=True, exist_ok=True)
    print(json.dumps(row), flush=True)
    with out.open("a") as fh:
        fh.write(json.dumps(row) + "\n")


def load(out: Path) -> list[dict]:
    return [json.loads(x) for x in out.read_text().splitlines() if x.strip()]
