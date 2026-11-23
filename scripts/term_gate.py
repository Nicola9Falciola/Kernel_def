#!/usr/bin/env python3
# Copyright (c) 2026 Nicola Falciola. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Nicola Falciola
"""The term gate: the terms the compiler produces, against a snapshot (adapted from
ModularSymbolsTau's `scripts/bench/kernel_form/term_gate.py`, with the same canonical form and
verdicts).

    python3 scripts/term_gate.py list
    python3 scripts/term_gate.py snapshot DIR
    python3 scripts/term_gate.py compare DIR [FILE.lean ...] [--map OLD=NEW ...]

`list` prints the `kernel_def`s of `KernelDef/` and `KernelDefTest/` (file, line, full name), read
off the sources; those that a test expects the compiler to reject (a `kernel_def`
under `#guard_msgs` whose expected message is an `error:`) are listed apart, and left out of
`snapshot` and `compare`.

`snapshot DIR` writes, for each of them, the type and the value of the constant of the present
build in a canonical form: constants by name, universe levels (the parameters of the definition
numbered), literals, de Bruijn indices; no binder name, no binder annotation, no metadata. One
JSON file a definition (`DIR/<name>.json`), with three more forms of the value: η-reduced, with
the `OfNat` numerals of `ℕ` as raw literals, and both; and `DIR/INDEX.json`, the list of them.
`test/golden/` is the snapshot of the repository (the list forms of `KernelDef/ListForms.lean` and
the definitions the tests accept): the baseline of a change of the compiler.

`compare DIR` does the same for the present build and compares, for every `kernel_def` of the
sources (of the given files only, when files are given), with the definition of the same name in
the snapshot. The verdicts:

* `identical`;
* `identical up to η` (of the outer `fun` and wherever `Expr.eta` reduces);
* `identical up to numerals` (an `OfNat` numeral against a raw literal), possibly with η;
* `DIFFERENT`, with the first place where the two values part;
* `TYPE CHANGED` when the type is not the one of the snapshot (an argument moved);
* `NEW`: the definition is not in the snapshot;
* `MISSING`: a definition of the snapshot is not among the sources (checked only when no file is
  given).

The exit code is 1 when a definition is not identical up to η (up to numerals for an entry whose
`todo` is true in the index), has a changed type, is new or is missing. To accept a change of the
compiler's output, take the snapshot again (`snapshot test/golden`) in the same change.

`--map OLD=NEW` (repeatable) compares under a renaming: a constant named `OLD` (or `OLD.x`) in the
snapshot is read as `NEW` (`NEW.x`), in the names of the definitions and inside the terms: for a
snapshot taken elsewhere (the port from ModularSymbolsTau was accepted against its snapshot with
`--map ModularSymbolsTau.Compute.Pack.listGetD=KernelDef.listGetD`, … for the names that moved).

`lean` runs once, through `lake env lean` from the repository root, on a file in a temporary
folder that imports the modules of the definitions: run `lake build` first.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
DIRS = ["KernelDef", "KernelDefTest"]
SKIP_FILES = {"KernelDef/KernelForm.lean"}
KDEF = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*"
                  r"kernel_def\s+([^\s({:\[]+)")
SCOPE = re.compile(r"^(?:noncomputable\s+)?(namespace|section|end)(?:\s+([\w.«»']+))?\s*$")
GUARD = re.compile(r"^#guard_msgs\b.*\bin\s*$")

LEAN = r'''
open Lean Meta

/-- A term without its metadata nodes (an `OfNat` numeral written as an argument of `Nat.add`
carries one around its type). -/
partial def noMData (e : Expr) : Expr :=
  e.replace fun e ↦ if e.isMData then some (noMData e.mdataExpr!) else none

/-- `OfNat` numerals of `ℕ` as raw literals. -/
def rawLits (e : Expr) : Expr :=
  e.replace fun e ↦
    if e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 0).isConstOf ``Nat &&
        (e.getArg! 1).isRawNatLit then some (e.getArg! 1) else none

/-- A term without names of binders, binder annotations or metadata. -/
partial def canon (e : Expr) : String :=
  match e with
  | .bvar i => s!"#{i}"
  | .const n ls =>
    if ls.isEmpty then toString n else s!"{n}.\{{", ".intercalate (ls.map toString)}}"
  | .app .. => "(" ++ " ".intercalate ((e.getAppFn :: e.getAppArgs.toList).map canon) ++ ")"
  | .lam _ d b _ => s!"(fun {canon d} => {canon b})"
  | .forallE _ d b _ => s!"(pi {canon d} => {canon b})"
  | .letE _ t v b _ => s!"(let {canon t} := {canon v} ; {canon b})"
  | .lit (.natVal n) => toString n
  | .lit (.strVal s) => s.quote
  | .sort l => s!"(Sort {l})"
  | .proj S i b => s!"(proj {S} {i} {canon b})"
  | .mdata _ b => canon b
  | .mvar _ => "?m"
  | .fvar _ => "?f"

def dump (out : System.FilePath) (names : List String) : MetaM Unit := do
  let env ← getEnv
  let wanted : Std.HashSet Name := names.foldl (fun s n ↦ s.insert n.toName) {}
  -- a private definition is found by the name its file gives it
  let byUser : Std.HashMap Name Name := env.constants.fold (init := {}) fun m n _ ↦
    match privateToUserName? n with
    | some u => if wanted.contains u then m.insert u n else m
    | none => m
  let mut missing : Array String := #[]
  for s in names do
    let user := s.toName
    let c := if env.contains user then user else byUser.getD user user
    let some (.defnInfo info) := env.find? c | missing := missing.push s; continue
    let ps := info.levelParams.mapIdx fun i _ ↦ Level.param (Name.mkSimple s!"p{i}")
    let v := noMData (info.value.instantiateLevelParams info.levelParams ps)
    let t := noMData (info.type.instantiateLevelParams info.levelParams ps)
    let j := Json.mkObj [("name", s), ("type", canon t), ("value", canon v),
      ("eta", canon v.eta), ("raw", canon (rawLits v)), ("etaraw", canon (rawLits v).eta)]
    IO.FS.writeFile (out / (s ++ ".json")) j.compress
  IO.FS.writeFile (out / "MISSING.json") (toJson missing).compress

'''


def kernel_defs() -> tuple[list[dict], list[dict]]:
    """The `kernel_def`s of the sources (file, module, full name, line; `todo` false), and apart
    those that a test expects to be rejected."""
    out, rejected = [], []
    for d in DIRS:
        for f in sorted((REPO / d).rglob("*.lean")):
            rel = f.relative_to(REPO)
            if str(rel) in SKIP_FILES:
                continue
            lines = f.read_text().split("\n")
            scopes: list[tuple[str, str]] = []
            i, comment = 0, False
            while i < len(lines):
                ln = lines[i]
                # the prose of a comment may start a line with `end` or `section`
                if comment or ("/-" in ln and "-/" not in ln.split("/-", 1)[1]):
                    comment = "-/" not in ln if comment else True
                    i += 1
                    continue
                m = SCOPE.match(ln)
                if m:
                    if m.group(1) == "end":
                        if scopes:
                            scopes.pop()
                    else:
                        scopes.append((m.group(1), m.group(2) or ""))
                mk = KDEF.match(ln)
                if mk:
                    short = re.sub(r"\.$", "", mk.group(1))  # `count.{u}`: the name is `count`
                    ns = ".".join(n for k, n in scopes if k == "namespace")
                    full = short[len("_root_."):] if short.startswith("_root_.") else (
                        f"{ns}.{short}" if ns else short)
                    entry = {"file": str(rel), "module": ".".join(rel.with_suffix("").parts),
                             "todo": False, "name": full, "line": i + 1}
                    (rejected if expects_error(lines, i) else out).append(entry)
                i += 1
    return out, rejected


def expects_error(lines: list[str], i: int) -> bool:
    """Whether the `kernel_def` at line `i` is under a `#guard_msgs` that expects an error."""
    k = i - 1
    if k >= 0 and lines[k].rstrip().endswith("-/"):  # its own docstring
        while k >= 0 and "/-" not in lines[k]:
            k -= 1
        k -= 1
    while k >= 0 and lines[k].startswith("@["):
        k -= 1
    if k < 0 or not GUARD.match(lines[k]):
        return False
    j = k - 1
    doc = []
    while j >= 0:
        doc.append(lines[j])
        if "/-" in lines[j]:
            break
        j -= 1
    return re.search(r"^(?:/--\s*)?error\b", "\n".join(reversed(doc)), re.M) is not None


def dump(defs: list[dict], out: Path) -> list[str]:
    """The canonical forms of `defs` in the present build, one JSON file each in `out`; the names
    not found."""
    out.mkdir(parents=True, exist_ok=True)
    mods = sorted({d["module"] for d in defs})
    names = ", ".join(json.dumps(d["name"]) for d in defs)
    src = ("\n".join(f"import {m}" for m in mods) + "\n" + LEAN +
           f"run_meta dump {json.dumps(str(out))} [{names}]\n")
    with tempfile.TemporaryDirectory() as tmp:
        f = Path(tmp) / "TermGate.lean"
        f.write_text(src)
        p = subprocess.run(["lake", "env", "lean", "-DmaxSynthPendingDepth=3",
                            "-DrelaxedAutoImplicit=false", str(f)], cwd=REPO,
                           capture_output=True, text=True)
        if p.returncode != 0 or p.stdout.strip():
            raise SystemExit(f"lean failed:\n{p.stdout[:3000]}{p.stderr[-2000:]}")
    return json.loads((out / "MISSING.json").read_text())


def parse_maps(args: list[str]) -> tuple[list[str], list[tuple[str, str]]]:
    rest, maps, i = [], [], 0
    while i < len(args):
        if args[i] == "--map" and i + 1 < len(args) and "=" in args[i + 1]:
            old, new = args[i + 1].split("=", 1)
            maps.append((old, new))
            i += 2
        elif args[i].startswith("--map="):
            old, new = args[i][len("--map="):].split("=", 1)
            maps.append((old, new))
            i += 1
        else:
            rest.append(args[i])
            i += 1
    return rest, maps


def rename(s: str, maps: list[tuple[str, str]]) -> str:
    """`s` with every constant `OLD` (or `OLD.x`) written `NEW` (`NEW.x`)."""
    for old, new in maps:
        s = re.sub(r"(^|[\s(])" + re.escape(old) + r"(?=$|[\s().])",
                   lambda m: m.group(1) + new, s)
    return s


def first_difference(a: str, b: str) -> str:
    ta, tb = a.split(), b.split()
    i = next((k for k, (x, y) in enumerate(zip(ta, tb)) if x != y), min(len(ta), len(tb)))
    return (f"at token {i}: was `{' '.join(ta[max(0, i - 4):i + 8])}`, "
            f"is `{' '.join(tb[max(0, i - 4):i + 8])}`")


def compare(snap: Path, files: list[str], maps: list[tuple[str, str]]) -> int:
    index = json.loads((snap / "INDEX.json").read_text())
    old_by = {rename(d["name"], maps): d for d in index}
    for f in files:
        if not Path(f).is_file():
            raise SystemExit(f"no such file: {f}")
    files = [str(Path(f).resolve().relative_to(REPO)) for f in files]
    defs, _ = kernel_defs()
    if files:
        defs = [d for d in defs if d["file"] in files]
        if not defs:
            raise SystemExit("no kernel_def in the files given")
    counts: dict[str, int] = {}
    bad = 0
    with tempfile.TemporaryDirectory() as tmp:
        missing_build = dump(defs, Path(tmp))
        for d in defs:
            name = d["name"]
            if name in missing_build:
                v, ok = "NOT BUILT (no such definition in the build)", False
            elif name not in old_by:
                v, ok = "NEW (not in the snapshot)", False
            else:
                o = old_by[name]
                old = json.loads((snap / f"{o['name']}.json").read_text())
                old = {k: rename(x, maps) for k, x in old.items()}
                new = json.loads((Path(tmp) / f"{name}.json").read_text())
                if new["type"] != old["type"]:
                    v, ok = "TYPE CHANGED: " + first_difference(old["type"], new["type"]), False
                elif new["value"] == old["value"]:
                    v, ok = "identical", True
                elif new["eta"] == old["eta"]:
                    v, ok = "identical up to η", True
                elif new["raw"] == old["raw"]:
                    v, ok = "identical up to numerals", o.get("todo", False)
                elif new["etaraw"] == old["etaraw"]:
                    v, ok = "identical up to numerals and η", o.get("todo", False)
                else:
                    v = "DIFFERENT, " + first_difference(old["raw"], new["raw"])
                    ok = o.get("todo", False)
            key = v.split(",")[0].split(":")[0].split(" (")[0]
            counts[key] = counts.get(key, 0) + 1
            bad += not ok
            print(f"{'ok  ' if ok else 'FAIL'} {name}: {v}")
        if not files:
            names = {d["name"] for d in defs}
            for n, o in old_by.items():
                if n not in names:
                    counts["MISSING"] = counts.get("MISSING", 0) + 1
                    bad += 1
                    print(f"FAIL {n}: MISSING (in the snapshot, not among the sources)")
    print(f"{len(defs)} compared: " + ", ".join(f"{n} {k}" for k, n in counts.items()) +
          f"; {bad} failing")
    return 1 if bad else 0


def main() -> None:
    a = sys.argv[1:]
    if a[:1] == ["list"]:
        defs, rejected = kernel_defs()
        for d in defs:
            print(f"{d['file']}:{d['line']}  {d['name']}")
        print(len(defs), "kernel_defs")
        for d in rejected:
            print(f"{d['file']}:{d['line']}  {d['name']}  (rejected, as its test expects)")
        print(len(rejected), "rejected by design")
    elif a[:1] == ["snapshot"] and len(a) == 2:
        defs, _ = kernel_defs()
        out = Path(a[1])
        for old in out.glob("*.json"):
            old.unlink()
        missing = dump(defs, out)
        (out / "MISSING.json").unlink()
        if missing:
            raise SystemExit(f"not in the build: {missing}")
        (out / "INDEX.json").write_text(json.dumps(defs, indent=1) + "\n")
        print(len(defs), "definitions written to", out)
    elif a[:1] == ["compare"] and len(a) >= 2:
        rest, maps = parse_maps(a[2:])
        sys.exit(compare(Path(a[1]), rest, maps))
    else:
        raise SystemExit(__doc__)


if __name__ == "__main__":
    main()
