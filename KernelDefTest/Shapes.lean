/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import KernelDef.KernelForm
import Mathlib.Data.Nat.Notation

/-!
# Shapes of definitions

Shapes beyond the 32 of ModularSymbolsTau's `Compute/Pack/Walk.lean`: two lists walked in step,
`let` and the tests on `ℕ`, a carried argument before or after the one recursed on, a match on a
pair, an option or a compound term, a user rule; each with the kernel form its `#guard_msgs`
expects. The compiled code of a kernel form is that of the readable definition (`#eval`).

Part of the test suite (library `KernelDefTest`): `lake build` fails when a message changes.
-/

-- the messages that `#guard_msgs` expects are as long as Lean prints them
set_option linter.style.longLine false

namespace KernelDefTest.Shapes

/-- Two lists walked in step, overlapping patterns. -/
kernel_def allZip {α β : Type*} (f : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && allZip f as bs
  | _, _ => false

/--
info: def KernelDefTest.Shapes.allZip.{u_1, u_2} : {α : Type u_1} →
  {β : Type u_2} → (α → β → Bool) → List α → List β → Bool :=
fun {α} {β} f x x_1 ↦
  @List.rec α (fun _ ↦ List β → Bool) (fun x ↦ @List.rec β (fun _ ↦ Bool) true (fun head tail tail_ih ↦ false) x)
    (fun head tail tail_ih x ↦
      @List.rec β (fun _ ↦ Bool) false
        (fun head_1 tail tail_ih_1 ↦ @Bool.rec (fun x ↦ Bool) false (tail_ih tail) (f head head_1)) x)
    x x_1
-/
#guard_msgs in
set_option pp.explicit true in
#print allZip

/-- info: 'KernelDefTest.Shapes.allZip.eq_src' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in
#print axioms allZip.eq_src

/-- A list walked with a counter. -/
kernel_def allIdx {α : Type*} (f : ℕ → α → Bool) : List α → ℕ → Bool
  | [], _ => true
  | a :: t, s => f s a && allIdx f t (s + 1)

/--
info: def KernelDefTest.Shapes.allIdx.{u_1} : {α : Type u_1} → (ℕ → α → Bool) → List α → ℕ → Bool :=
fun {α} f x x_1 ↦
  List.rec (motive := fun _ ↦ ℕ → Bool) (fun x ↦ true)
    (fun head tail tail_ih x ↦ Bool.rec false (tail_ih (x.add 1)) (f x head)) x x_1
-/
#guard_msgs in
#print allIdx

kernel_def allLt (P : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | n + 1 => P n && allLt P n

/--
info: def KernelDefTest.Shapes.allLt : (ℕ → Bool) → ℕ → Bool :=
fun P x ↦ Nat.rec true (fun n n_ih ↦ Bool.rec false n_ih (P n)) x
-/
#guard_msgs in
#print allLt

/-- `let`, `<`, `≠`, `∧`, `∨`, `¬`, `==`, `!=`, a Boolean as a condition. -/
kernel_def tests (a b c : ℕ) (t : Bool) : ℕ :=
  let s := a + b * c
  if s < c ∧ a ≠ b then s
  else if a = b ∨ ¬ b ≤ c then s ^ 2
  else if t then a ||| b
  else if a != c && t || a == 7 then a ^^^ b else 0

/--
info: def KernelDefTest.Shapes.tests : ℕ → ℕ → ℕ → Bool → ℕ :=
fun a b c t ↦
  Bool.rec
    (Bool.rec
      (Bool.rec (Bool.rec 0 (a.xor b) (Bool.rec (a.beq 7) true (Bool.rec false t (Bool.rec true false (a.beq c)))))
        (a.lor b) t)
      ((a.add (b.mul c)).pow 2) (Bool.rec (Bool.rec true false (b.ble c)) true (a.beq b)))
    (a.add (b.mul c)) (Bool.rec false (Bool.rec true false (a.beq b)) ((a.add (b.mul c)).blt c))
-/
#guard_msgs in
#print tests

/-- info: 'KernelDefTest.Shapes.tests.eq_src' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in
#print axioms tests.eq_src

/-- The argument after the one recursed on is not changed: it is not carried. -/
kernel_def powAcc (b : ℕ) : ℕ → ℕ → ℕ
  | 0, m => m
  | n + 1, m => b * powAcc b n m

/--
info: def KernelDefTest.Shapes.powAcc : ℕ → ℕ → ℕ → ℕ :=
fun b x x_1 ↦ Nat.rec (motive := fun _ ↦ ℕ → ℕ) (fun x ↦ x) (fun n n_ih x ↦ b.mul (n_ih x)) x x_1
-/
#guard_msgs in
#print powAcc

/-- A carried argument before the one recursed on. -/
kernel_def sumTo : ℕ → ℕ → ℕ
  | acc, 0 => acc
  | acc, n + 1 => sumTo (acc + n) n

/--
info: def KernelDefTest.Shapes.sumTo : ℕ → ℕ → ℕ :=
fun x x_1 ↦ Nat.rec (motive := fun _ ↦ ℕ → ℕ) (fun x ↦ x) (fun n n_ih x ↦ n_ih (x.add n)) x_1 x
-/
#guard_msgs in
#print sumTo

/-- A match on a pair, and on an option. -/
kernel_def swapAdd (p : ℕ × ℕ) (o : Option ℕ) : ℕ :=
  match p, o with
  | (a, b), some c => a + b + c
  | (a, _), none => a

/--
info: def KernelDefTest.Shapes.swapAdd : ℕ × ℕ → Option ℕ → ℕ :=
fun p o ↦ Prod.rec (fun fst snd ↦ Option.rec fst (fun val ↦ (fst.add snd).add val) o) p
-/
#guard_msgs in
#print swapAdd

/-- info: 'KernelDefTest.Shapes.swapAdd.eq_src' does not depend on any axioms -/
#guard_msgs in
#print axioms swapAdd.eq_src

/-- A match on a compound term. -/
kernel_def onTerm (a b : ℕ) : ℕ :=
  match a - b with
  | 0 => b
  | n + 1 => n

/--
info: def KernelDefTest.Shapes.onTerm : ℕ → ℕ → ℕ :=
fun a b ↦ Nat.rec b (fun n n_ih ↦ n) (a.sub b)
-/
#guard_msgs in
#print onTerm

/-- Computable: the compiled code is that of the readable definition. -/
example : allLt (fun i ↦ i < 10) 10 = true := by decide +kernel

/-- info: 7 -/
#guard_msgs in
#eval tests 3 4 5 true

/-- info: true -/
#guard_msgs in
#eval allZip (fun (a b : ℕ) ↦ a == b) [1, 2, 3] [1, 2, 3]

/-- A user rule. -/
def twice (f : ℕ → ℕ) (x : ℕ) : ℕ := f (f x)
@[kernel_rule] theorem twice_eq (f : ℕ → ℕ) (x : ℕ) : twice f x = f (f x) := rfl
kernel_def useTwice (x : ℕ) : ℕ := twice (fun y ↦ y * 3 + 1) x

/--
info: def KernelDefTest.Shapes.useTwice : ℕ → ℕ :=
fun x ↦ (((x.mul 3).add 1).mul 3).add 1
-/
#guard_msgs in
#print useTwice

end KernelDefTest.Shapes
