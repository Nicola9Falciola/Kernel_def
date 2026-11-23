#!/usr/bin/env bash
# Copyright (c) 2026 Nicola Falciola. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Nicola Falciola

# The test suite of the compiler, run from anywhere; exits non-zero when a gate fails.
#
#   scripts/run_tests.sh            all the gates
#   NO_BENCH=1 scripts/run_tests.sh  without the elaboration of the files of `bench/`
#
# The gates:
#   1. `lake build` (the compiler and the tests): no error, no warning;
#   2. `scripts/term_gate.py compare test/golden`: every kernel form as in the snapshot;
#   3. `KernelDefTest/Axioms.lean` imports every module of `KernelDefTest/` and `Audit.lean` every
#      one but `Axioms.lean`, so that the axiom check and the audit cover every test;
#   4. no `sorry`, `admit` or `native_decide` in the Lean sources, comments left out;
#   5. every file of `bench/` elaborates with no error (`lake env lean`).
# Every gate runs, and the summary names those that failed. Heavy: one at a time on the machine.
set -u
cd "$(dirname "$0")/.."
failed=()
log=$(mktemp "${TMPDIR:-/tmp}/kernel_def_build.XXXXXX")

echo "== 1. lake build"
if lake build >"$log" 2>&1; then
  if /usr/bin/grep -E "warning|⚠" "$log"; then failed+=("build warnings"); fi
  /usr/bin/grep -E "Build completed" "$log"
else
  /usr/bin/grep -E "error|✖" "$log" | head -40
  failed+=("lake build")
fi
rm -f "$log"

echo "== 2. term gate"
if python3 scripts/term_gate.py compare test/golden >"${TMPDIR:-/tmp}/kernel_def_gate.txt" 2>&1; then
  tail -1 "${TMPDIR:-/tmp}/kernel_def_gate.txt"
else
  /usr/bin/grep -v "^ok  " "${TMPDIR:-/tmp}/kernel_def_gate.txt" | head -40
  failed+=("term gate")
fi

echo "== 3. imports of the audit and the axiom check"
if ! python3 - <<'EOF'
import re, sys
from pathlib import Path
mods = {".".join(f.with_suffix("").parts) for f in Path("KernelDefTest").rglob("*.lean")}
bad = 0
for t, skip in (("KernelDefTest/Axioms.lean", {"KernelDefTest.Axioms"}),
                ("KernelDefTest/Audit.lean", {"KernelDefTest.Axioms", "KernelDefTest.Audit"})):
    imps = set(re.findall(r"^import\s+(\S+)", Path(t).read_text(), re.M))
    miss = sorted(mods - skip - imps)
    if miss:
        print(f"{t} does not import: {', '.join(miss)}")
        bad = 1
print("every module of KernelDefTest/ covered" if not bad else "", end="")
print()
sys.exit(bad)
EOF
then failed+=("imports of the audit"); fi

echo "== 4. no sorry, admit or native_decide"
if ! python3 - <<'EOF'
import re, sys
from pathlib import Path

def code(text: str) -> str:
    """`text` without its comments (nested block comments, line comments) and string literals."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif depth and text.startswith("-/", i):
            depth, i = depth - 1, i + 2
        elif depth:
            i += 1
        elif text.startswith("--", i):
            i = text.find("\n", i) if "\n" in text[i:] else len(text)
        elif text[i] == '"':
            j = i + 1
            while j < len(text) and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            i = j + 1
        else:
            out.append(text[i])
            i += 1
    return "".join(out)

bad = 0
files = [Path("KernelDef.lean")] + [f for d in ("KernelDef", "KernelDefTest", "bench")
                                    for f in sorted(Path(d).rglob("*.lean"))]
for f in files:
    for m in re.finditer(r"(?<![\w.'])(sorry|admit|native_decide)(?![\w'])", code(f.read_text())):
        print(f"{f}: {m.group(1)}")
        bad = 1
print(f"{len(files)} files clean" if not bad else "")
sys.exit(bad)
EOF
then failed+=("sorry or native_decide"); fi

if [ -z "${NO_BENCH:-}" ]; then
  echo "== 5. the files of bench/ elaborate"
  for f in bench/*.lean; do
    out=$(lake env lean -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false "$f" 2>&1)
    if [ $? -ne 0 ] || [ -n "$out" ]; then
      echo "$f:"; echo "$out" | head -20
      failed+=("bench $f")
    fi
  done
  echo "$(ls bench/*.lean | wc -l | tr -d ' ') files checked"
fi

echo
if [ ${#failed[@]} -eq 0 ]; then
  echo "all gates passed"
else
  echo "FAILED: ${failed[*]}"
  exit 1
fi
