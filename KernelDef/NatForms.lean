/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import KernelDef.KernelForm
import Mathlib.Data.Nat.Notation

/-!
# Kernel forms of functions on `ℕ`

`Nat.log2` is no primitive of the kernel in Lean `v4.37.0-rc1`: the kernel runs its definition, a
`Nat.rec` on the argument that takes one step a bit (about 57 k instructions a bit). `Nat.sqrt`
computes its first guess with `Nat.log2`, then iterates by well-founded recursion
(`WellFounded.Nat.fix`, which the kernel reduces through a fuel). `Nat.testBit`, `min`, `max`,
`Nat.pred` and `Nat.lcm` go through instances, `ite` or a matcher at every use. `Nat.all n f` and
`decide (∀ i < n, p i)` wrap the predicate once a step, so that the kernel evaluates them in
quadratic time and memory. Each has here a kernel form and a `@[kernel_rule]`; measured in
`docs/library_forms/README.md`.

## Main definitions

* `natLog2` — `Nat.log2` by a binary search on the bit length (`log2Up` doubles, `log2Desc`
  halves): `O(log log n)` steps, each one shift.
* `natSqrt` — `Nat.sqrt`, Newton's iteration on a fuel (`sqrtIterFuel`), its first guess through
  `natLog2`.
* `natTestBit` — bit `j` of `m`: a shift, a mask and a `Nat.beq`.
* `natAll` — `∀ i < n, f i` as a bare `Nat.rec`.

## Main results

* `log2_eq_natLog2`, `sqrt_eq_natSqrt`, `testBit_eq_natTestBit`, `min_eq_ite`, `max_eq_ite`,
  `pred_eq_sub_one`, `lcm_eq_mul_div_gcd`, `all_eq_natAll`, `decide_forall_lt_eq_natAll` — the
  `@[kernel_rule]`s.

## Order of the rules

The rule on `Nat.log2` comes before the definition of `natSqrt`, whose source calls `n.log2`: a
`kernel_def` is compiled with the rules declared before it, so the kernel form of `natSqrt` calls
`natLog2`. The right side of a rule must not call its left side (the compiler translates the right
side again): `natLog2` bounds its search by a fuel, not by a fallback to `Nat.log2`. Across modules
the order does not matter: no rule of `ListForms`, `NatForms`, `IntForms` or `MathlibForms`
matches a term that a rule of another of them matches (their rules on `decide` are on different
propositions), so the order of the imports of `KernelDef.lean` does not change a kernel form.

## Place in the pipeline

Imports the compiler and the notation `ℕ` only; `KernelDef.lean` imports it with the list forms
(`KernelDef/ListForms.lean`) and the forms of `ℤ` (`KernelDef/IntForms.lean`).
-/

namespace KernelDef

section Log2

/-- The bits of `log2 n` below `2 ^ k`, those above being `r`. -/
kernel_def log2Desc (n : ℕ) : ℕ → ℕ → ℕ
  | 0, r => r
  | k + 1, r => if n >>> (r + (1 <<< k)) = 0 then log2Desc n k r else log2Desc n k (r + (1 <<< k))

/-- The least `k ≥ k₀` with `n < 2 ^ 2 ^ k`, by doubling (the fuel bounds the steps), then
`log2Desc`. -/
kernel_def log2Up (n : ℕ) : ℕ → ℕ → ℕ
  | 0, k => log2Desc n k 0
  | fuel + 1, k => if n >>> (1 <<< k) = 0 then log2Desc n k 0 else log2Up n fuel (k + 1)

/-- `Nat.log2 n`; the fuel `n` is never exhausted, since `n < 2 ^ 2 ^ n`. -/
kernel_def natLog2 (n : ℕ) : ℕ := log2Up n n 0

theorem shiftRight_eq_zero_iff_lt (n s : ℕ) : n >>> s = 0 ↔ n < 2 ^ s := by
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff]
  have := Nat.two_pow_pos s
  omega

theorem log2_eq_of_lt (n r : ℕ) (h₀ : (n = 0 ∧ r = 0) ∨ 2 ^ r ≤ n) (h₁ : n < 2 ^ (r + 1)) :
    n.log2 = r := by
  rcases h₀ with ⟨rfl, rfl⟩ | h₀
  · rfl
  · have hn : n ≠ 0 := by have := Nat.two_pow_pos r; omega
    exact Nat.le_antisymm (Nat.lt_succ_iff.mp ((Nat.log2_lt hn).mpr h₁)) ((Nat.le_log2 hn).mpr h₀)

theorem log2Desc_eq (n k r : ℕ) (h₀ : (n = 0 ∧ r = 0) ∨ 2 ^ r ≤ n)
    (h₁ : n < 2 ^ (r + 2 ^ k)) : log2Desc n k r = n.log2 := by
  induction k generalizing r with
  | zero => rw [log2Desc]; exact (log2_eq_of_lt n r h₀ (by simpa using h₁)).symm
  | succ k ih =>
    rw [log2Desc, Nat.one_shiftLeft]
    split
    next h => exact ih r h₀ ((shiftRight_eq_zero_iff_lt _ _).mp h)
    next h =>
      rw [shiftRight_eq_zero_iff_lt, Nat.not_lt] at h
      rw [Nat.pow_succ, Nat.mul_two, ← Nat.add_assoc] at h₁
      exact ih _ (Or.inr h) h₁

theorem log2_inv_zero (n : ℕ) : (n = 0 ∧ 0 = 0) ∨ 2 ^ 0 ≤ n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr h

theorem log2Up_eq (n fuel k : ℕ) (h : n < 2 ^ 2 ^ (k + fuel)) : log2Up n fuel k = n.log2 := by
  induction fuel generalizing k with
  | zero => rw [log2Up]; exact log2Desc_eq n k 0 (log2_inv_zero n) (by simpa using h)
  | succ fuel ih =>
    rw [log2Up, Nat.one_shiftLeft]
    split
    next hk =>
      exact log2Desc_eq n k 0 (log2_inv_zero n)
        (by simpa using (shiftRight_eq_zero_iff_lt _ _).mp hk)
    next => exact ih (k + 1) (by rwa [show k + 1 + fuel = k + (fuel + 1) by omega])

@[kernel_rule]
theorem log2_eq_natLog2 : Nat.log2 = natLog2 := by
  funext n
  rw [natLog2, log2Up_eq]
  have h : n < 2 ^ n := Nat.lt_two_pow_self
  simpa using Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt h))

end Log2

section Sqrt

/-- Newton's iteration of `Nat.sqrt.iter`, with a fuel in place of the well-founded recursion. -/
kernel_def sqrtIterFuel (n : ℕ) : ℕ → ℕ → ℕ
  | 0, guess => guess
  | fuel + 1, guess =>
    if (guess + n / guess) / 2 < guess then sqrtIterFuel n fuel ((guess + n / guess) / 2)
    else guess

theorem sqrtIterFuel_eq (n fuel guess : ℕ) (h : guess < fuel) :
    sqrtIterFuel n fuel guess = Nat.sqrt.iter n guess := by
  induction fuel generalizing guess with
  | zero => omega
  | succ fuel ih =>
    rw [sqrtIterFuel, Nat.sqrt.iter.eq_1]
    dsimp only
    split
    next => exact ih _ (by omega)
    next => rfl

/-- `Nat.sqrt n`, from the guess `2 ^ (log2 n / 2 + 1)` as in the core, with the fuel the
well-founded recursion uses (`guess + 1`); its `n.log2` is `natLog2 n`. -/
kernel_def natSqrt (n : ℕ) : ℕ :=
  if n ≤ 1 then n else sqrtIterFuel n ((1 <<< (n.log2 / 2 + 1)) + 1) (1 <<< (n.log2 / 2 + 1))

@[kernel_rule]
theorem sqrt_eq_natSqrt : Nat.sqrt = natSqrt := by
  funext n
  rw [natSqrt, Nat.sqrt]
  split
  next => rfl
  next => exact (sqrtIterFuel_eq _ _ _ (Nat.lt_succ_self _)).symm

end Sqrt

section Scalars

/-- Bit `j` of `m`: a shift, a mask and a `Nat.beq`. -/
kernel_def natTestBit (m j : ℕ) : Bool := m >>> j &&& 1 == 1

@[kernel_rule]
theorem testBit_eq_natTestBit : Nat.testBit = natTestBit := by
  funext m j
  rw [natTestBit, Nat.testBit_eq_decide_div_mod_eq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rfl

/-- `min` at `ℕ` (`instMinNat`); the compiler writes the `if` as a `Bool.rec` on `Nat.ble`. -/
@[kernel_rule]
theorem min_eq_ite (a b : ℕ) : min a b = if a ≤ b then a else b := Nat.min_def

/-- `max` at `ℕ` (`Nat.instMax`). -/
@[kernel_rule]
theorem max_eq_ite (a b : ℕ) : max a b = if a ≤ b then b else a := Nat.max_def

@[kernel_rule]
theorem pred_eq_sub_one (n : ℕ) : n.pred = n - 1 := rfl

@[kernel_rule]
theorem lcm_eq_mul_div_gcd (m n : ℕ) : Nat.lcm m n = m * n / Nat.gcd m n := rfl

end Scalars

section Bounded

kernel_def natAll : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, f => natAll n f && f n

/-- `Nat.all n f` when `f` does not use its proof of `i < n` (the rule's left side is the
pattern `fun i _ ↦ f i`). -/
@[kernel_rule]
theorem all_eq_natAll (n : ℕ) (f : ℕ → Bool) : (Nat.all n fun i _ ↦ f i) = natAll n f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Nat.all_succ, ih, natAll]

/-- `decide (∀ i < n, p i)`, decided by `Nat.decidableBallLT` in the core. -/
@[kernel_rule]
theorem decide_forall_lt_eq_natAll (n : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    decide (∀ i < n, p i) = natAll n fun i ↦ decide (p i) := by
  induction n with
  | zero => simp [natAll]
  | succ n ih =>
    rw [natAll, ← ih, ← Bool.decide_and, decide_eq_decide]
    constructor
    · exact fun h ↦ ⟨fun i hi ↦ h i (by omega), h n (by omega)⟩
    · rintro ⟨h, hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact hn

end Bounded

end KernelDef
