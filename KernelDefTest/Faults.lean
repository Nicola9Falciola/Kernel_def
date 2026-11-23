/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import KernelDef.KernelForm
import Mathlib.Data.Nat.Notation

/-!
# Faults of a readable definition, attributes, numerals

The behaviours of `kernel_def` the review of the prototype asked for, and the ones the tree's
compiler added: an error of the readable definition adds nothing; an attribute goes to the kernel
form; a numeral of `ℕ` is a raw literal wherever it stands.

Part of the test suite (library `KernelDefTest`): `lake build` fails when a message changes.
-/

-- the messages that `#guard_msgs` expects are as long as Lean prints them
set_option linter.style.longLine false

namespace KernelDefTest.Faults

/-- A hand-written form, as the files not yet migrated hold them. -/
noncomputable def hand (n : ℕ) : ℕ := Nat.rec (motive := fun _ ↦ ℕ) (nat_lit 0) (fun k _ ↦ k) n

/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on 'hand', which is 'noncomputable'
-/
#guard_msgs in
/-- The readable definition calls a `noncomputable` form and is not marked: its compilation
fails, and nothing is added. -/
kernel_def bad (n : ℕ) : ℕ := hand n + 1

/-- info: Unknown identifier `bad` -/
#guard_msgs in
#check_failure bad

/-- info: Unknown identifier `Src.bad` -/
#guard_msgs in
#check_failure Src.bad

/-- Marked `noncomputable`, it is accepted. -/
noncomputable kernel_def good (n : ℕ) : ℕ := hand n + 1

/--
info: def KernelDefTest.Faults.good : ℕ → ℕ :=
fun n ↦ (hand n).add 1
-/
#guard_msgs in
#print good

/-- An attribute is put on the kernel form. -/
@[simp] kernel_def twice (n : ℕ) : ℕ := 2 * n

example (n : ℕ) : twice n = n + n := by simp; omega

/-- Numerals: raw under a notation and under a primitive written as such. -/
kernel_def nums (n : ℕ) : ℕ := Nat.add (n + 1) 1 + Nat.succ 0

/--
info: def KernelDefTest.Faults.nums : ℕ → ℕ :=
fun n ↦ ((n.add (nat_lit 1)).add (nat_lit 1)).add (Nat.succ (nat_lit 0))
-/
#guard_msgs in
set_option pp.natLit true in
#print nums

end KernelDefTest.Faults
