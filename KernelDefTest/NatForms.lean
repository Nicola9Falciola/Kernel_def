/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import KernelDef

/-!
# The forms of `ℕ` in use

A readable definition calls `n.log2`, `n.sqrt`, `n.testBit k`, `min`, `max`, `n.pred`, `Nat.lcm`,
`Nat.all` and `decide (∀ i < n, p i)`; with `KernelDef/NatForms.lean` imported, its kernel form
calls `natLog2`, `natSqrt`, `natTestBit`, `natAll`, or a `Bool.rec` on `Nat.ble`, through the
`@[kernel_rule]`s, and `#kernel_audit strict` finds no miss. Also: a plain definition that calls
`Nat.log2` (no rule rewrites it) is reported by the audit, since `Nat.log2` is no primitive of the
kernel.

Part of the test suite (library `KernelDefTest`): `lake build` fails when a message changes.
-/

namespace KernelDefTest.NatForms

section Calls

kernel_def lg (n : ℕ) : ℕ := n.log2

/--
info: def KernelDefTest.NatForms.lg : ℕ → ℕ :=
fun n ↦ KernelDef.natLog2 n
-/
#guard_msgs in
#print lg

kernel_def isqrt (n : ℕ) : ℕ := n.sqrt

/--
info: def KernelDefTest.NatForms.isqrt : ℕ → ℕ :=
fun n ↦ KernelDef.natSqrt n
-/
#guard_msgs in
#print isqrt

kernel_def bit3 (n : ℕ) : Bool := n.testBit 3

/-- `min` and `max`: a `Bool.rec` on `Nat.ble` each; the inner `min` is one shared term. -/
kernel_def clamp (lo hi x : ℕ) : ℕ := max lo (min hi x)

/--
info: def KernelDefTest.NatForms.clamp : ℕ → ℕ → ℕ → ℕ :=
fun lo hi x ↦ Bool.rec lo (Bool.rec x hi (hi.ble x)) (lo.ble (Bool.rec x hi (hi.ble x)))
-/
#guard_msgs in
#print clamp

kernel_def before (n : ℕ) : ℕ := n.pred

kernel_def lcm12 (n : ℕ) : ℕ := Nat.lcm n 12

kernel_def noSquareAll (n : ℕ) : Bool := Nat.all n fun i _ ↦ i * i != 7

/-- `decide (∀ i < n, p i)`: `natAll`, the predicate decided at each `i`. -/
kernel_def noSquareBelow (n m : ℕ) : Bool := decide (∀ i < n, i * i ≠ m)

/--
info: def KernelDefTest.NatForms.noSquareBelow : ℕ → ℕ → Bool :=
fun n m ↦ KernelDef.natAll n fun i ↦ Bool.rec true false ((i.mul i).beq m)
-/
#guard_msgs in
#print noSquareBelow

/--
info: kernel audit of 8: 0 with a miss of the compiler, 0 more with a representation it keeps
misses: none
representation: none
-/
#guard_msgs in
#kernel_audit strict lg isqrt bit3 clamp before lcm12 noSquareAll noSquareBelow

example : lg 1000000 = 19 ∧ lg 0 = 0 ∧ lg 1 = 0 := by decide +kernel
example : lg (2 ^ 4096) = 4096 ∧ lg (2 ^ 4096 - 1) = 4095 := by decide +kernel
example : isqrt 1000000 = 1000 ∧ isqrt 999999 = 999 ∧ isqrt 1 = 1 ∧ isqrt 0 = 0 := by
  decide +kernel
example : isqrt (10 ^ 200) = 10 ^ 100 := by decide +kernel
example : bit3 8 = true ∧ bit3 7 = false := by decide +kernel
example : clamp 3 10 1 = 3 ∧ clamp 3 10 20 = 10 ∧ clamp 3 10 5 = 5 := by decide +kernel
example : before 10 = 9 ∧ before 0 = 0 := by decide +kernel
example : lcm12 18 = 36 ∧ lcm12 0 = 0 := by decide +kernel
example : noSquareAll 1000 = true := by decide +kernel
example : noSquareBelow 1000 50 = true ∧ noSquareBelow 10 49 = false := by decide +kernel

end Calls

section NoPrimitive

/-- A plain definition, which no rule rewrites: the call of `Nat.log2` is a miss, since the
kernel runs its definition, one step a bit, and the audit no longer counts it as a primitive. -/
def plainLog2 (n : ℕ) : ℕ := n.log2

/--
info: kernel audit of 1: 1 with a miss of the compiler, 0 more with a representation it keeps
misses: library function in 1 (1 subterm)
representation: none
  plainLog2: misses: library function: Nat.log2 ×1
-/
#guard_msgs in
#kernel_audit plainLog2

end NoPrimitive

end KernelDefTest.NatForms
