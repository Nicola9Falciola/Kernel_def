/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import KernelDef.MathlibForms

/-!
# The forms of Mathlib's functions in use

With the optional module `KernelDef/MathlibForms.lean` imported, a readable definition that calls
`decide (Nat.Prime p)`, `Nat.fib`, `Nat.factorial` or `Nat.digits` compiles to `natPrime`,
`natFibAux`, `natFactorial`, `natDigits`; `#kernel_audit strict` finds no miss. `Nat.digits 10 n`
compiles to `natDigits 10 n`, the base kept a literal.

Part of the test suite (library `KernelDefTest`): `lake build` fails when a message changes.
-/

namespace KernelDefTest.MathlibForms

kernel_def isPrime (p : ℕ) : Bool := decide (Nat.Prime p)

/--
info: def KernelDefTest.MathlibForms.isPrime : ℕ → Bool :=
fun p ↦ KernelDef.natPrime p
-/
#guard_msgs in
#print isPrime

kernel_def fibOf (n : ℕ) : ℕ := n.fib

kernel_def fact (n : ℕ) : ℕ := n.factorial

kernel_def decimal (n : ℕ) : List ℕ := Nat.digits 10 n

/--
info: def KernelDefTest.MathlibForms.decimal : ℕ → List ℕ :=
fun n ↦ KernelDef.natDigits 10 n
-/
#guard_msgs in
#print decimal

kernel_def digitsIn (b n : ℕ) : List ℕ := Nat.digits b n

/--
info: kernel audit of 5: 0 with a miss of the compiler, 0 more with a representation it keeps
misses: none
representation: none
-/
#guard_msgs in
#kernel_audit strict isPrime fibOf fact decimal digitsIn

example : isPrime 1000003 = true ∧ isPrime 1000001 = false ∧ isPrime 1 = false ∧
    isPrime 2 = true := by
  decide +kernel
example : fibOf 100 = 354224848179261915075 := by decide +kernel
example : fact 20 = 2432902008176640000 := by decide +kernel
example : decimal 1234 = [4, 3, 2, 1] ∧ digitsIn 2 6 = [0, 1, 1] ∧ digitsIn 1 3 = [1, 1, 1] ∧
    digitsIn 0 7 = [7] ∧ digitsIn 10 0 = [] := by
  decide +kernel

end KernelDefTest.MathlibForms
