/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import KernelDef.KernelForm
import Mathlib.Data.Int.Notation

/-!
# Kernel forms of the arithmetic of `ℤ`

The kernel evaluates `+`, `-`, `*`, `/`, `%` on `ℤ` through `Int.add`, `Int.sub`, … : matchers on
the constructors, `Int.subNatNat` and `Int.negOfNat` (matchers again) and the instance arithmetic
of `ℕ` inside. `decide (a < b)` goes through `Int.decLt`, that is `decNonneg (b - (a + 1))`, and
`decide (a = b)` through `Int.decEq`. The core of Lean `v4.37.0-rc1` gives kernel forms of the
arithmetic, with their proofs (`Init/Data/Int/Kernel.lean`: `Int.add_k`, `Int.mul_k`, …, written
with `Int.rec`, `Bool.rec` and the primitives of `ℕ`); this file states them as
`@[kernel_rule]`s, with `Int.blt'` for the comparisons and a kernel form of the equality.

The compiler does not change representation: a kernel form still computes on `ℤ`, and
`#kernel_audit` lists these forms (`Int.add_k`, …) as representation, not as misses.

## Main definitions

* `intBEq` — `a = b` on `ℤ`, a `Nat.beq` of the two magnitudes when the signs agree.

## Main results

* `int_add_eq`, `int_mul_eq`, `int_sub_eq`, `int_neg_eq`, `int_natAbs_eq`, `int_emod_eq`,
  `int_ediv_eq`, `int_toNat_eq` — the kernel forms of the core, as rules;
* `int_decide_lt`, `int_decide_le`, `int_decide_eq` — the comparisons.

## Place in the pipeline

Imports the compiler and the notation `ℤ` only; `KernelDef.lean` imports it. The compiler writes
the primitives of `ℕ` for the notation on `ℕ` itself, before it looks for a rule; these rules are
found for the notation on `ℤ`, and match no term that a rule of another module matches.
-/

namespace KernelDef

section Arith

@[kernel_rule] theorem int_add_eq (a b : ℤ) : a + b = Int.add_k a b := (Int.add_k_eq a b).symm
@[kernel_rule] theorem int_mul_eq (a b : ℤ) : a * b = Int.mul_k a b := (Int.mul_k_eq a b).symm
@[kernel_rule] theorem int_sub_eq (a b : ℤ) : a - b = Int.sub_k a b := (Int.sub_k_eq a b).symm
@[kernel_rule] theorem int_neg_eq (a : ℤ) : -a = Int.neg_k a := (Int.neg_k_eq a).symm

@[kernel_rule]
theorem int_natAbs_eq (a : ℤ) : a.natAbs = Int.natAbs_k a := (Int.natAbs_k_eq a).symm

@[kernel_rule]
theorem int_emod_eq (a b : ℤ) : a % b = Int.emod_k a b := (Int.emod_k_eq a b).symm

@[kernel_rule]
theorem int_ediv_eq (a b : ℤ) : a / b = Int.ediv_k a b := (Int.ediv_k_eq a b).symm

@[kernel_rule]
theorem int_toNat_eq (a : ℤ) : a.toNat = Int.toNat_k a := (Int.toNat_k_eq a).symm

end Arith

section Compare

@[kernel_rule]
theorem int_decide_lt (a b : ℤ) : decide (a < b) = Int.blt' a b := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Int.blt'_eq_true]

@[kernel_rule]
theorem int_decide_le (a b : ℤ) : decide (a ≤ b) = !Int.blt' b a := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, Bool.not_eq_true', Int.blt'_eq_false, Int.not_lt]

kernel_def intBEq : ℤ → ℤ → Bool
  | .ofNat m, .ofNat n => m == n
  | .negSucc m, .negSucc n => m == n
  | _, _ => false

@[kernel_rule]
theorem int_decide_eq (a b : ℤ) : decide (a = b) = intBEq a b := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  cases a <;> cases b <;> simp [intBEq, Int.ofNat_inj]

end Compare

end KernelDef
