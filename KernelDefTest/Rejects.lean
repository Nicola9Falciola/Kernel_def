/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import KernelDef.KernelForm
import Mathlib.Data.Nat.Notation

/-!
# What the compiler rejects

Each rejected `kernel_def` below fails with the error that its `#guard_msgs` expects, and adds
nothing (`#check_failure`): well-founded recursion, a recursive call two constructors down, the
function passed as an argument. A proof used in the code is accepted, and its `dite` stays in the
kernel form (`#kernel_audit` reports it: `KernelDefTest/Audit.lean`).

Part of the test suite (library `KernelDefTest`): `lake build` fails when a message changes.
-/

-- the messages that `#guard_msgs` expects are as long as Lean prints them
set_option linter.style.longLine false

namespace KernelDefTest.Rejects

/--
error: kernel_def `halve` rejected: kernel form: `KernelDefTest.Rejects.Src.halve` is not defined by structural recursion
-/
#guard_msgs in
/-- Well-founded recursion. -/
kernel_def halve (n : ℕ) : ℕ := if n < 2 then 0 else 1 + halve (n / 2)

/--
error: kernel_def `fib` rejected: kernel form: the recursive call
  Src.fib n
is not on a field of the constructor matched
-/
#guard_msgs in
/-- A recursive call two constructors down. -/
kernel_def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- error: fail to show termination for
  KernelDefTest.Rejects.Src.mapTwice -/
#guard_msgs (substring := true) in
/-- The function itself passed as an argument. -/
kernel_def mapTwice : List ℕ → List ℕ
  | [] => []
  | a :: t => a :: (List.map (fun l ↦ (mapTwice l).length) [t])

/-- A proof used in the code. -/
kernel_def getOr (l : List ℕ) (i : ℕ) : ℕ := if h : i < l.length then l[i] else 0

/-- info: Unknown identifier `halve` -/
#guard_msgs in
#check_failure halve

/-- info: Unknown identifier `fib` -/
#guard_msgs in
#check_failure fib

/-- info: Unknown identifier `mapTwice` -/
#guard_msgs in
#check_failure mapTwice

/--
info: def KernelDefTest.Rejects.getOr : List ℕ → ℕ → ℕ :=
fun l i ↦ if h : i < l.length then l[i] else 0
-/
#guard_msgs in
#print getOr

end KernelDefTest.Rejects
