/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import KernelDef
import KernelDefTest.Accepts
import KernelDefTest.Audit
import KernelDefTest.DocExamples
import KernelDefTest.Faults
import KernelDefTest.IntForms
import KernelDefTest.LibraryForms
import KernelDefTest.MathlibForms
import KernelDefTest.NatForms
import KernelDefTest.Rejects
import KernelDefTest.Shapes
import KernelDefTest.Syntax

/-!
# The axioms of the compiled definitions and of the tests

Every kernel form of the environment (those of the modules of `KernelDef/` and of the tests), the
theorems the compiler generated for it (`f.eq_src`, `f.src_eq`, `f.eq_src_fun`, `f.eq_def`,
`f.eq_1 …`), and every declaration of the modules of `KernelDef/` and `KernelDefTest/`, rest on
no axiom but `propext`, `Classical.choice` and `Quot.sound`: no `sorry` (`sorryAx`), no
`native_decide` (the auxiliary axiom it adds). The check fails the build otherwise, naming the
declarations at fault; it prints nothing when it passes.

Part of the test suite (library `KernelDefTest`); `scripts/run_tests.sh` checks that this file
imports every module of `KernelDefTest/` but itself.
-/

open Lean Meta KernelDef

namespace KernelDefTest.Axioms

/-- The declarations the check reads: every kernel form with the theorems generated for it, and
every declaration of the modules whose root is `KernelDef` or `KernelDefTest`; and the number of
kernel forms. -/
def checkedDecls : MetaM (Array Name × Nat) := do
  let env ← getEnv
  let mut out : Array Name := #[]
  let mut nForms := 0
  for (k, _) in (pairExt.getState env).snd do
    nForms := nForms + 1
    out := out ++ #[k, k ++ `eq_src, k ++ `src_eq, k ++ `eq_src_fun, k ++ `eq_def]
    let mut i := 1
    while env.contains (k ++ Name.mkSimple s!"eq_{i}") do
      out := out.push (k ++ Name.mkSimple s!"eq_{i}")
      i := i + 1
  for n in out do
    unless env.contains n do throwError "missing {n}"
  for name in env.header.moduleNames, data in env.header.moduleData do
    if [`KernelDef, `KernelDefTest].contains name.getRoot then out := out ++ data.constNames
  return (out, nForms)

run_meta do
  let (decls, nForms) ← checkedDecls
  if nForms == 0 then throwError "no kernel form in the environment"
  let mut bad : Array (Name × Name) := #[]
  for n in decls do
    for a in ← collectAxioms n do
      unless allowedAxioms.contains a do bad := bad.push (n, a)
  unless bad.isEmpty do
    throwError "declarations resting on an axiom outside the allowed ones: {bad.toList}"

end KernelDefTest.Axioms
