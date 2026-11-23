/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import KernelDef
import KernelDef.MathlibForms

/-!
# The terms of the library forms, for the benchmark of `libbench.py`

Writes the kernel form of every `kernel_def` of the library (`KernelDef/ListForms.lean`,
`NatForms.lean`, `IntForms.lean`, `MathlibForms.lean`), fully explicit (`pp.all`, raw literals),
to the file named by the environment variable `LIBFORMS_EXPORT`: one block a definition,
`### name.{universes}`, its type, its value. `scripts/library_forms/libbench.py` reads them back as
`noncomputable def`s, so that its files import nothing and measure the compiler's own terms. Not
part of a library: `libbench.py export` runs it, after `lake build`.
-/

open Lean Meta KernelDef

run_meta do
  let some path ← IO.getEnv "LIBFORMS_EXPORT"
    | throwError "Export.lean: set LIBFORMS_EXPORT to the file to write"
  let env ← getEnv
  let forms := (pairExt.getState env).snd.toArray.map (·.fst) |>.filter fun n ↦
    match env.getModuleIdxFor? n with
    | some i => env.header.moduleNames[i.toNat]!.getRoot == `KernelDef
    | none => false
  let opts := ((← getOptions).setBool `pp.all true).setBool `pp.natLit true
    |>.insert `format.width (DataValue.ofNat 1000000)
  -- every form after the forms it calls
  let mut order : Array Name := #[]
  let mut pending := forms.qsort (·.toString < ·.toString)
  while !pending.isEmpty do
    let mut next := #[]
    for n in pending do
      let deps := (← getConstInfo n).value!.getUsedConstants.filter forms.contains
      if deps.all order.contains then order := order.push n else next := next.push n
    if next.size == pending.size then throwError "Export.lean: the forms call one another"
    pending := next
  let mut out := ""
  for n in order do
    let ci ← getConstInfo n
    let ty ← withOptions (fun _ ↦ opts) (ppExpr ci.type)
    let val ← withOptions (fun _ ↦ opts) (ppExpr ci.value!)
    let us := if ci.levelParams.isEmpty then "" else
      ".{" ++ ", ".intercalate (ci.levelParams.map toString) ++ "}"
    out := out ++ s!"### {n}{us}\n{ty}\n{val}\n"
  IO.FS.writeFile path out
