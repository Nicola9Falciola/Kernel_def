/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import KernelDef
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.Prime.Basic

/-!
# Kernel forms of functions of Mathlib on `ℕ`

An optional module: `KernelDef.lean` does not import it, since a client pays for every import and
these need Mathlib's number theory. A client that calls the functions below in a `kernel_def`
imports `KernelDef.MathlibForms`.

`decide (Nat.Prime p)` runs Mathlib's instance `Nat.decidablePrime`, a bounded quantifier over
every `m < p`: `O(p)` steps, with memory that grows with `p` (the kernel needs more than 24 GB at
`p = 16381`). `Nat.fib` iterates on pairs through `Nat.iterate`, `Nat.factorial` is structural
recursion with `HMul`, and `Nat.digits` is well-founded recursion (`WellFounded.Nat.fix`, which
the kernel reduces through a fuel). Measured in `docs/library_forms/README.md`.

## Main definitions

* `natPrime` — trial division up to `√p` (`noDivFrom`, the fuel `p`).
* `natFibAux` — `fib` by two accumulators.
* `natFactorial` — the product, a bare `Nat.rec`.
* `natDigits` — the digits in every base (`digitsFuel`, the fuel `n + 1`, for bases from `2`).

## Main results

* `decide_prime_eq_natPrime`, `fib_eq_natFibAux`, `factorial_eq_natFactorial`,
  `digits_eq_natDigits` — the `@[kernel_rule]`s.

## The rule on `Nat.digits`

It is stated for every base. A rule `Nat.digits (b + 2) n = …` would match `Nat.digits 10 n` by
unifying `10` with `?b + 2` and leave `Nat.add 8 2` in the kernel form. The bases `0` and `1` are
written out in `natDigits`, since a right side that called `Nat.digits` would be rewritten by the
rule itself.

## Place in the pipeline

Imports `KernelDef.lean` (so that every rule of the library is in scope here) and four modules of
Mathlib.
-/

namespace KernelDef

section Prime

/-- No divisor of `p` among `d, d + 1, …` up to `√p`; the fuel bounds the steps. -/
kernel_def noDivFrom (p : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | fuel + 1, d => if p < d * d then true else p % d != 0 && noDivFrom p fuel (d + 1)

theorem noDivFrom_iff (p fuel d : ℕ) (hd : 0 < d) (h : p < d + fuel) :
    noDivFrom p fuel d = true ↔ ∀ m, d ≤ m → m * m ≤ p → ¬m ∣ p := by
  induction fuel generalizing d with
  | zero =>
    simp only [noDivFrom, true_iff]
    intro m hm hmm
    nlinarith
  | succ fuel ih =>
    rw [noDivFrom]
    split_ifs with hp
    · simp only [true_iff]
      intro m hm hmm
      nlinarith
    · rw [Bool.and_eq_true, ih (d + 1) (by omega) (by omega), bne_iff_ne, ne_eq,
        ← Nat.dvd_iff_mod_eq_zero]
      constructor
      · rintro ⟨hdvd, hrest⟩ m hm hmm
        rcases Nat.eq_or_lt_of_le hm with rfl | hlt
        · exact hdvd
        · exact hrest m hlt hmm
      · intro hall
        exact ⟨hall d le_rfl (by omega), fun m hm hmm ↦ hall m (by omega) hmm⟩

kernel_def natPrime (p : ℕ) : Bool := 2 ≤ p && noDivFrom p p 2

/-- `decide (Nat.Prime p)`, with Mathlib's instance `Nat.decidablePrime`. -/
@[kernel_rule]
theorem decide_prime_eq_natPrime (p : ℕ) : decide (Nat.Prime p) = natPrime p := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, natPrime, Bool.and_eq_true, decide_eq_true_iff]
  by_cases hp : 2 ≤ p
  · rw [noDivFrom_iff p p 2 (by norm_num) (by omega), Nat.prime_def_le_sqrt]
    simp only [hp, true_and]
    exact ⟨fun h m hm hmm ↦ h m hm (Nat.le_sqrt.mpr hmm),
      fun h m hm hms ↦ h m hm (Nat.le_sqrt.mp hms)⟩
  · simp only [hp, false_and, iff_false]
    exact fun h ↦ hp h.two_le

end Prime

section Fib

kernel_def natFibAux : ℕ → ℕ → ℕ → ℕ
  | 0, a, _ => a
  | n + 1, a, b => natFibAux n b (a + b)

theorem natFibAux_fib (n k : ℕ) :
    natFibAux n (Nat.fib k) (Nat.fib (k + 1)) = Nat.fib (n + k) := by
  induction n generalizing k with
  | zero => simp [natFibAux]
  | succ n ih =>
    rw [natFibAux, ← Nat.fib_add_two, ih (k + 1)]
    ring_nf

@[kernel_rule]
theorem fib_eq_natFibAux (n : ℕ) : Nat.fib n = natFibAux n 0 1 := by
  simpa using (natFibAux_fib n 0).symm

end Fib

section Factorial

kernel_def natFactorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * natFactorial n

@[kernel_rule]
theorem factorial_eq_natFactorial : Nat.factorial = natFactorial := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.factorial_succ, natFactorial, ih]

end Factorial

section Digits

/-- The digits of `n` in base `b`, the fuel bounding their number (`n + 1` will do). -/
kernel_def digitsFuel (b : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else n % b :: digitsFuel b fuel (n / b)

theorem digitsFuel_eq (b fuel n : ℕ) (h : n < fuel) :
    digitsFuel (b + 2) fuel n = Nat.digits (b + 2) n := by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
    rw [digitsFuel]
    split_ifs with h0
    · simp [h0]
    · have hn : 0 < n := Nat.pos_of_ne_zero h0
      rw [Nat.digits_def' (by omega : 1 < b + 2) hn,
        ih (n / (b + 2)) (lt_of_lt_of_le (Nat.div_lt_self hn (by omega)) (by omega))]

kernel_def natDigits (b n : ℕ) : List ℕ :=
  if b = 0 then (if n = 0 then [] else [n])
  else if b = 1 then List.replicate n 1
  else digitsFuel b (n + 1) n

@[kernel_rule]
theorem digits_eq_natDigits : Nat.digits = natDigits := by
  funext b n
  rw [natDigits]
  match b with
  | 0 => cases n <;> simp
  | 1 => simp [Nat.digits_one]
  | b + 2 => simp [digitsFuel_eq b (n + 1) n (Nat.lt_succ_self n)]

end Digits

end KernelDef
