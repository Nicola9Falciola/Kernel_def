/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import KernelDef.KernelForm
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Notation

/-!
# What the compiler accepts since step 5

What the compiler accepts since step 5 (ModularSymbolsTau, `docs/bench/kernel_form/README.md`,
"Step 5: three improvements of the compiler") and rejected before. Each `kernel_def` below is
added, with its equation `f.eq_src`, and the kernel decides each `example`; the kernel forms are
those the `#guard_msgs` expect.

* Structural recursion on a list whose elements are an `abbrev` of a list (`List Row`, `Row` a
  list of pairs): the recursive fields of a constructor are read off the recursor, and the head of
  a cons is no longer taken for one.
* A recursive call on a constructor rebuilt from the fields of a case on the field matched
  (`y :: rows` after matching `x :: y :: rows`, `n + 1` after matching `n + 2`): it is the call on
  that field.

Part of the test suite (library `KernelDefTest`): `lake build` fails when a message changes.
-/

-- the messages that `#guard_msgs` expects are as long as Lean prints them
set_option linter.style.longLine false

namespace KernelDefTest.Accepts

abbrev Row := List (ℕ × ℤ)

/-- The number of entries of a list of rows. -/
kernel_def entries : List Row → ℕ
  | [] => 0
  | r :: t => r.length + entries t

abbrev Rows := List Row

/-- The same, on the `abbrev` itself. -/
kernel_def entries' : Rows → ℕ
  | [] => 0
  | r :: t => r.length + entries' t

/--
info: def KernelDefTest.Accepts.entries : List Row → ℕ :=
fun x ↦ List.rec 0 (fun head tail tail_ih ↦ (List.rec 0 (fun x x_1 ih ↦ ih.add 1) head).add tail_ih) x
-/
#guard_msgs in
#print entries

/--
info: def KernelDefTest.Accepts.entries' : Rows → ℕ :=
fun x ↦ List.rec 0 (fun head tail tail_ih ↦ (List.rec 0 (fun x x_1 ih ↦ ih.add 1) head).add tail_ih) x
-/
#guard_msgs in
#print entries'

example : entries [[(1, 2), (3, -1)], [], [(0, 5)]] = 3 := by decide +kernel
example : entries' [[(1, 2)], [(0, 5)]] = 2 := by decide +kernel

/-- Consecutive elements, with a call on `y :: rows` after matching `x :: y :: rows`. The patterns
overlap: the match is split case by case. -/
kernel_def steps (b : ℕ) : List ℕ → List ℕ → Bool
  | x :: y :: rows, q :: W => x + b == y + q && steps b (y :: rows) W
  | [], _ => true
  | [_], _ => true
  | _, _ => false

/-- The same without overlapping patterns: the match is a chain of `casesOn`. -/
kernel_def pairSum : List ℕ → ℕ
  | [] => 0
  | [x] => x
  | x :: y :: t => x * y + pairSum (y :: t)

/-- A rebuilt `Nat.succ n`, written `n + 1`. -/
kernel_def tri : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => n + 2 + tri (n + 1)

/--
info: def KernelDefTest.Accepts.steps : ℕ → List ℕ → List ℕ → Bool :=
fun b x x_1 ↦
  List.rec (motive := fun _ ↦ List ℕ → Bool) (fun x ↦ true)
    (fun head tail tail_ih x ↦
      List.rec true
        (fun head_1 tail tail_ih_1 ↦
          List.rec false
            (fun head_2 tail tail_ih_2 ↦ Bool.rec false (tail_ih tail) ((head.add b).beq (head_1.add head_2))) x)
        tail)
    x x_1
-/
#guard_msgs in
#print steps

/-- info: 'KernelDefTest.Accepts.steps.eq_src' depends on axioms: [propext, Classical.choice] -/
#guard_msgs in
#print axioms steps.eq_src

/--
info: def KernelDefTest.Accepts.pairSum : List ℕ → ℕ :=
fun x ↦
  List.rec 0 (fun head tail tail_ih ↦ List.rec head (fun head_1 tail tail_ih_1 ↦ (head.mul head_1).add tail_ih) tail) x
-/
#guard_msgs in
#print pairSum

/--
info: def KernelDefTest.Accepts.tri : ℕ → ℕ :=
fun x ↦ Nat.rec 0 (fun n n_ih ↦ Nat.rec 1 (fun n n_ih_1 ↦ (n.add 2).add n_ih) n) x
-/
#guard_msgs in
#print tri

example : steps 0 [5, 4, 3] [1, 1] = true := by decide +kernel
example : steps 0 [5, 4, 3] [1, 2] = false := by decide +kernel
example : steps 0 [5, 4, 3] [1] = false := by decide +kernel
example : pairSum [1, 2, 3] = 11 := by decide +kernel
example : tri 4 = 10 := by decide +kernel

end KernelDefTest.Accepts
