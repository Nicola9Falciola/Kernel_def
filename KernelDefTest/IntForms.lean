/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import KernelDef

/-!
# The forms of `ℤ` in use

A readable definition computes on `ℤ` (`+`, `-`, `*`, `/`, `%`, `natAbs`, `toNat`, `<`, `≤`, `=`);
with `KernelDef/IntForms.lean` imported, its kernel form calls the kernel forms of the core
(`Int.add_k`, …, `Int.blt'`) and `intBEq`. The audit lists them as representation (`Int`), not
as misses: the compiler does not change representation.

Part of the test suite (library `KernelDefTest`): `lake build` fails when a message changes.
-/

namespace KernelDefTest.IntForms

kernel_def iadd (a b : ℤ) : ℤ := a + b

kernel_def isub (a b : ℤ) : ℤ := a - b

kernel_def imul (a b : ℤ) : ℤ := a * b

kernel_def ineg (a : ℤ) : ℤ := -a

kernel_def iabs (a : ℤ) : ℕ := a.natAbs

kernel_def imod (a b : ℤ) : ℤ := a % b

kernel_def idiv (a b : ℤ) : ℤ := a / b

kernel_def itoNat (a : ℤ) : ℕ := a.toNat

kernel_def ilt (a b : ℤ) : Bool := decide (a < b)

/--
info: def KernelDefTest.IntForms.ilt : ℤ → ℤ → Bool :=
fun a b ↦ a.blt' b
-/
#guard_msgs in
#print ilt

kernel_def ile (a b : ℤ) : Bool := decide (a ≤ b)

kernel_def ieq (a b : ℤ) : Bool := decide (a = b)

/-- A fold on `ℤ`: `Int.mul_k` and `Int.add_k` in a bare `List.rec`; the numeral stays. -/
kernel_def dot : List (ℤ × ℤ) → ℤ
  | [] => 0
  | p :: l => p.fst * p.snd + dot l

/--
info: def KernelDefTest.IntForms.dot : List (ℤ × ℤ) → ℤ :=
fun x ↦ List.rec 0 (fun head tail tail_ih ↦ (head.fst.mul_k head.snd).add_k tail_ih) x
-/
#guard_msgs in
#print dot

/--
info: kernel audit of 12: 0 with a miss of the compiler, 11 more with a representation it keeps
misses: none
representation: Int in 11 (13 subterms), pairs in 1 (2 subterms)
  iadd: representation: Int: Int.add_k ×1
  isub: representation: Int: Int.sub_k ×1
  imul: representation: Int: Int.mul_k ×1
  ineg: representation: Int: Int.neg_k ×1
  iabs: representation: Int: Int.natAbs_k ×1
  imod: representation: Int: Int.emod_k ×1
  idiv: representation: Int: Int.ediv_k ×1
  itoNat: representation: Int: Int.toNat_k ×1
  ilt: representation: Int: Int.blt' ×1
  ile: representation: Int: Int.blt' ×1
  dot: representation: Int: Int.add_k ×1, Int.mul_k ×1, OfNat.ofNat ×1; pairs: Prod.fst ×1, Prod.snd ×1
-/
#guard_msgs in
#kernel_audit strict iadd isub imul ineg iabs imod idiv itoNat ilt ile ieq dot

example : iadd 3 (-5) = -2 ∧ isub (-3) 4 = -7 ∧ imul (-6) 7 = -42 ∧ ineg 5 = -5 := by
  decide +kernel
example : iabs (-9) = 9 ∧ imod (-7) 3 = 2 ∧ idiv (-7) 3 = -3 ∧ itoNat (-4) = 0 := by
  decide +kernel
example : ilt (-3) 2 = true ∧ ile 2 2 = true ∧ ile 3 2 = false ∧ ieq (-4) (-4) = true ∧
    ieq 4 (-4) = false := by
  decide +kernel
example : dot [(2, -3), (-4, -5)] = 14 := by decide +kernel

end KernelDefTest.IntForms
