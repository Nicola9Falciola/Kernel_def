/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import KernelDef.KernelForm
import Mathlib.Data.Nat.Notation

/-!
# `kernel_def` among the modifiers and surroundings of an ordinary `def`

A section variable, a docstring and an attribute; explicit universes; `private` and `protected`;
a helper defined with `where`, which is a second definition and is not compiled.

Part of the test suite (library `KernelDefTest`): `lake build` fails when a message changes.
-/

namespace KernelDefTest.Syn

section
variable {α : Type*} (K : ℕ)

/-- A section variable, a docstring and an attribute. -/
@[simp] kernel_def packAll (f : α → ℕ) : List α → ℕ
  | [] => 0
  | a :: t => f a + packAll f t <<< K

/-- info: @packAll : {α : Type u_2} → ℕ → (α → ℕ) → List α → ℕ -/
#guard_msgs in
#check @packAll

/--
info: @packAll.eq_2 : ∀ {α : Type u_2} (K : ℕ) (f : α → ℕ) (a : α) (t : List α),
  packAll K f (a :: t) = f a + packAll K f t <<< K
-/
#guard_msgs in
#check @packAll.eq_2
end

/-- Explicit universes. -/
kernel_def count.{u} {β : Type u} : List β → ℕ → ℕ
  | [], n => n
  | _ :: t, n => count t (n + 1)

/-- `private` and `protected`. -/
private kernel_def hidden (n : ℕ) : ℕ := n * n + 1
protected kernel_def Nat.sq (n : ℕ) : ℕ := n * n

example : hidden 3 = 10 := by decide +kernel
example : Syn.Nat.sq 3 = 9 := by decide +kernel
example : packAll 4 (fun x : ℕ ↦ x) [1, 2, 3] = 0x321 := by decide +kernel
example (l : List ℕ) : count l 0 = l.length := by
  suffices h : ∀ n, count l n = l.length + n from h 0
  induction l with
  | nil => intro n; simp [count]
  | cons a t ih => intro n; rw [count, ih]; simp; omega

/-- A helper defined with `where`: a second definition, not compiled. -/
kernel_def total (l : List ℕ) : ℕ := go l 0
where go : List ℕ → ℕ → ℕ
  | [], acc => acc
  | a :: t, acc => go t (acc + a)

/--
info: def KernelDefTest.Syn.total : List ℕ → ℕ :=
fun l ↦ Src.total.go l 0
-/
#guard_msgs in
#print total

/-- info: 'KernelDefTest.Syn.total.eq_src' does not depend on any axioms -/
#guard_msgs in
#print axioms total.eq_src

end KernelDefTest.Syn
