/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import KernelDef.IntForms
import KernelDef.KernelForm
import KernelDef.ListForms
import KernelDef.NatForms

/-!
# `kernel_def`: kernel forms compiled from readable definitions

The library's root: the compiler (`KernelDef/KernelForm.lean`: `kernel_def`, `@[kernel_inline]`,
`@[kernel_rule]`, `#kernel_audit`) and the kernel forms of library functions, with their rules:
the functions of the core on lists, arrays and `Option`, and `Nat.choose`
(`KernelDef/ListForms.lean`), on `ℕ` (`KernelDef/NatForms.lean`) and on `ℤ`
(`KernelDef/IntForms.lean`). A client imports this file. The forms of functions of Mathlib's
number theory (`Nat.Prime`, `Nat.fib`, `Nat.factorial`, `Nat.digits`) are in
`KernelDef/MathlibForms.lean`, which a client imports apart: this file does not, since every
client pays for every import.
-/
