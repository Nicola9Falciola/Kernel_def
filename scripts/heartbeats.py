#!/usr/bin/env python3
# Copyright (c) 2026 Nicola Falciola. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Nicola Falciola
"""The elaboration cost of the compiler, declaration by declaration, in heartbeats (adapted from
ModularSymbolsTau's `scripts/bench/kernel_form/step4_heartbeats.py` and the heartbeats of
`plain_ab.py`).

    python3 scripts/heartbeats.py run OUT.jsonl TAG [FILE.lean ...]
    python3 scripts/heartbeats.py report OUT.jsonl TAG_A TAG_B

`run`: each file (by default every file of `KernelDefTest/` and `bench/`) is copied
into `KERNEL_DEF_WORK/hb/TAG/` (default: `kernel_def_work` in the system's temporary folder) with
Mathlib's `#count_heartbeats in` before every `kernel_def` and before every declaration that holds
`decide +kernel` (a theorem, a lemma, an `example`), its docstring, attributes and the prefixes
`#guard_msgs … in`, `set_option … in`, `omit … in` included: the counter wraps the guard, so a
guarded message (the error of a rejected definition) still matches, and its count is that of the
attempt. The copy is run once with the options of `meter.py` (single-threaded, `Elab.async` off,
so that the kernel's checks are counted; `pp.unicode.fun`, so that a guarded `#print` matches). One row a declaration, appended to `OUT`: `file`, `name` (an `example` is
`example#k`, the `k`-th of its file), `kind` (`kernel_def` or `decide`), `line` in the file,
`hb` (the thousands of small allocations of the command, elaboration and kernel: a count that does
not vary from run to run), with `tag`, `commit` and `compiler` (`meter.compiler_id`); a file that
fails gives one row with `error`. A `kernel_def`'s `hb` is the cost of the compiler on it (with the
elaboration of the readable definition and the kernel's check of the equations); a `decide`'s is
the cost of the check through the kernel forms.

`report` prints the totals by kind and by file of the two tags, then every declaration whose `hb`
moved, largest change first (`TOP` rows, all when `TOP` is unset). Run `lake build` first. Every
run is heavy: one at a time on the machine.
"""

from __future__ import annotations

import json
import os
import re
import sys
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from meter import REPO, WORK, append, compiler_id, load, run_lean  # noqa: E402

DEFAULT_DIRS = ["KernelDefTest", "bench"]
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|"
                  r"unsafe|scoped)\s+)*(kernel_def|theorem|lemma|example|def|abbrev|instance)\b"
                  r"\s*([^\s:({\[]*)")
PREFIX = re.compile(r"^(?:#guard_msgs|set_option|omit|include)\b.*\bin\s*$")
ATTR = re.compile(r"^@\[[^\]]*\]\s*$")
CONT = re.compile(r"^(?:where|termination_by|decreasing_by|deriving|\|)\b")
IMPORT = re.compile(r"^import\s+\S+", re.M)


def comments(lines: list[str]) -> list[tuple[int, int, str]]:
    """The comments of a file: (first line, last line, opening), nested comments counted once."""
    out, depth, start, opening = [], 0, 0, ""
    for i, ln in enumerate(lines):
        j = 0
        while j < len(ln):
            if ln.startswith("/-", j):
                if depth == 0:
                    start, opening = i, ln[j:j + 3]
                depth += 1
                j += 2
            elif ln.startswith("-/", j) and depth > 0:
                depth -= 1
                if depth == 0:
                    out.append((start, i, opening))
                j += 2
            elif depth == 0 and ln.startswith("--", j):
                break
            else:
                j += 1
    return out


def decls(text: str) -> list[dict]:
    """The declarations to count: `kernel_def`s, and declarations holding `decide +kernel`; each
    with the line where its command starts (docstring, attributes and prefixes included)."""
    lines = text.split("\n")
    cs = comments(lines)
    inside = {}  # line -> the comment that covers it
    for c in cs:
        for k in range(c[0], c[1] + 1):
            inside[k] = c

    def is_start(k: int) -> bool:
        ln = lines[k]
        return bool(ln) and not ln[0].isspace() and k not in inside and not CONT.match(ln)
    starts = [k for k in range(len(lines)) if is_start(k)]
    out, nex = [], 0
    for idx, k in enumerate(starts):
        m = DECL.match(lines[k])
        if not m:
            continue
        end = next((s for s in starts[idx + 1:]), len(lines))
        # its code, comments left out (the docstring of the next declaration is among them)
        block = "\n".join(lines[j] for j in range(k, end) if j not in inside)
        kind = "kernel_def" if m.group(1) == "kernel_def" else (
            "decide" if "decide +kernel" in block else None)
        if kind is None:
            continue
        if m.group(1) == "example":
            nex += 1
            name = f"example#{nex}"
        else:
            name = m.group(2)
        top, moved = k, True
        while moved:
            moved = False
            above = top - 1
            if above >= 0 and above in inside and inside[above][1] == above and \
                    inside[above][2] == "/--":
                top, moved = inside[above][0], True
            elif above >= 0 and (ATTR.match(lines[above]) or PREFIX.match(lines[above])):
                top, moved = above, True
        out.append({"name": name, "kind": kind, "line": k + 1, "top": top})
    return out


def instrument(text: str) -> tuple[str, dict[int, dict]]:
    """`text` with `#count_heartbeats in` before every declaration of `decls`, and the import of
    `Mathlib.Util.CountHeartbeats`; the declaration of each marker, by its line in the copy."""
    ds = decls(text)
    lines = text.split("\n")
    tops = {d["top"]: d for d in ds}
    out: list[str] = []
    for k, ln in enumerate(lines):
        if k in tops:
            out.append("#count_heartbeats in")
        out.append(ln)
    body = "\n".join(out)
    last = [m.end() for m in IMPORT.finditer(body)]
    at = last[-1] if last else 0
    body = body[:at] + "\nimport Mathlib.Util.CountHeartbeats" + body[at:]
    markers: dict[int, dict] = {}
    for k, ln in enumerate(body.split("\n")):
        if ln == "#count_heartbeats in":
            markers[k + 1] = None  # filled in order below
    for line, d in zip(sorted(markers), sorted(ds, key=lambda d: d["top"])):
        markers[line] = d
    return body, markers


def default_files() -> list[Path]:
    return sorted(f for d in DEFAULT_DIRS for f in (REPO / d).rglob("*.lean"))


def run(out: Path, tag: str, files: list[str]) -> None:
    ident = compiler_id()
    paths = [Path(f).resolve() for f in files] if files else default_files()
    for f in paths:
        rel = str(f.relative_to(REPO))
        body, markers = instrument(f.read_text())
        if not markers:
            continue
        copy = WORK / "hb" / tag / rel
        copy.parent.mkdir(parents=True, exist_ok=True)
        copy.write_text(body)
        base = {"date": time.strftime("%Y-%m-%d %H:%M"), "tag": tag, **ident, "file": rel}
        r = run_lean(copy, extra=["--json"])
        msgs = []
        for ln in r.get("out", "").splitlines():
            try:
                msgs.append(json.loads(ln))
            except json.JSONDecodeError:
                pass
        errs = [m for m in msgs if m.get("severity") == "error"]
        used = {m["pos"]["line"]: int(mm.group(1)) for m in msgs
                if (mm := re.match(r"Used (\d+) heartbeats", m.get("data", "")))}
        if errs or ("error" in r and "limit" in r) or set(used) != set(markers):
            err = (errs[0]["data"] if errs else r.get("error", "")) or \
                f"{len(used)} counts for {len(markers)} declarations"
            append(out, base | {"error": err[:1500]})
            continue
        for line, d in markers.items():
            append(out, base | {"name": d["name"], "kind": d["kind"], "line": d["line"],
                                "hb": used[line]})


def report(out: Path, a: str, b: str) -> None:
    rows = [r for r in load(out) if "hb" in r and r["tag"] in (a, b)]
    by = {(r["tag"], r["file"], r["kind"], r["name"]): r["hb"] for r in rows}
    keys = list(dict.fromkeys((r["file"], r["kind"], r["name"]) for r in rows))
    print(f"| kind | declarations | hb {a} | hb {b} | change |")
    print("|---|---:|---:|---:|---:|")
    for kind in ("kernel_def", "decide"):
        ks = [k for k in keys if k[1] == kind and (a,) + k in by and (b,) + k in by]
        ta, tb = sum(by[(a,) + k] for k in ks), sum(by[(b,) + k] for k in ks)
        ch = f"{tb - ta:+d}" + (f" ({(tb - ta) / ta:+.1%})" if ta else "")
        print(f"| {kind} | {len(ks)} | {ta} | {tb} | {ch} |")
    only = [k for k in keys if ((a,) + k in by) != ((b,) + k in by)]
    if only:
        print(f"\n{len(only)} declarations in one tag only (left out of the totals): " +
              ", ".join(f"{k[0]}:{k[2]}" for k in only[:20]) + (" …" if len(only) > 20 else ""))
    print(f"\n| file | hb {a} | hb {b} | change |")
    print("|---|---:|---:|---:|")
    for f in dict.fromkeys(k[0] for k in keys):
        ks = [k for k in keys if k[0] == f and (a,) + k in by and (b,) + k in by]
        if ks:
            ta, tb = sum(by[(a,) + k] for k in ks), sum(by[(b,) + k] for k in ks)
            print(f"| {f} | {ta} | {tb} | {tb - ta:+d} |")
    moved = [(k, by[(a,) + k], by[(b,) + k]) for k in keys
             if (a,) + k in by and (b,) + k in by and by[(a,) + k] != by[(b,) + k]]
    moved.sort(key=lambda x: abs(x[2] - x[1]), reverse=True)
    top = int(os.environ.get("TOP", "0")) or len(moved)
    print(f"\n{len(moved)} declarations moved" + (f", the {top} largest:" if top < len(moved)
                                                     else ":"))
    print(f"| file | declaration | kind | hb {a} | hb {b} | change |")
    print("|---|---|---|---:|---:|---:|")
    for (f, kind, name), ha, hb in moved[:top]:
        pct = f" ({(hb - ha) / ha:+.1%})" if ha else ""
        print(f"| {f} | `{name}` | {kind} | {ha} | {hb} | {hb - ha:+d}{pct} |")


def main() -> None:
    a = sys.argv[1:]
    if a[:1] == ["run"] and len(a) >= 3:
        run(Path(a[1]), a[2], a[3:])
    elif a[:1] == ["report"] and len(a) == 4:
        report(Path(a[1]), a[2], a[3])
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
