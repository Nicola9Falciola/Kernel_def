/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import KernelDef
import KernelDefTest.Shapes

/-!
# The examples of `docs/KERNEL_DEF.md`

The snippets that `docs/KERNEL_DEF.md` writes out, with every output it quotes (the kernel forms
`#print` shows, the equations, the reports of `#kernel_audit`) pinned by `#guard_msgs`: the build
fails when the compiler's output changes, and the document is then brought back in step with this
file. The two examples it takes from `KernelDefTest/Shapes.lean` (`allZip`, `sumTo`) are printed
here as the document quotes them.

* `sumSmall`, against `sumSmallHand`, the same term written by hand; `sumSmall_zero_right`, a lemma
  proved from the readable equations.
* `splitsOk`, with the `@[kernel_inline]` helpers `low` and `high`.
* `mask` and `field`, a definition without recursion that calls another kernel form.
* `sumL`, recursion on a list; `scale`, a match on an integer, its pairs kept.

Part of the test suite (library `KernelDefTest`): `lake build` fails when a message changes.
-/

-- the messages that `#guard_msgs` expects are as long as Lean prints them
set_option linter.style.longLine false

namespace KernelDefTest.DocExamples

section HandWritten

/-- The sum of the `n` slots of `K` bits of `x` that are at most `t`. -/
kernel_def sumSmall (K t : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, x =>
    if x &&& (1 <<< K - 1) ≤ t then (x &&& (1 <<< K - 1)) + sumSmall K t n (x >>> K)
    else sumSmall K t n (x >>> K)

/-- `sumSmall` written by hand in the fast form. -/
noncomputable def sumSmallHand (K t : ℕ) : ℕ → ℕ → ℕ :=
  @Nat.rec (fun _ ↦ ℕ → ℕ) (fun _ ↦ nat_lit 0)
    (fun _ ih x ↦
      @Bool.rec (fun _ ↦ ℕ) (ih (Nat.shiftRight x K))
        (Nat.add (Nat.land x (Nat.sub (Nat.shiftLeft (nat_lit 1) K) (nat_lit 1)))
          (ih (Nat.shiftRight x K)))
        (Nat.ble (Nat.land x (Nat.sub (Nat.shiftLeft (nat_lit 1) K) (nat_lit 1))) t))

example : @sumSmall = @sumSmallHand := rfl

/--
info: def KernelDefTest.DocExamples.sumSmall : ℕ → ℕ → ℕ → ℕ → ℕ :=
fun K t x x_1 ↦
  Nat.rec (motive := fun _ ↦ ℕ → ℕ) (fun x ↦ nat_lit 0)
    (fun n n_ih x ↦
      Bool.rec (n_ih (x.shiftRight K))
        ((x.land ((Nat.shiftLeft (nat_lit 1) K).sub (nat_lit 1))).add (n_ih (x.shiftRight K)))
        ((x.land ((Nat.shiftLeft (nat_lit 1) K).sub (nat_lit 1))).ble t))
    x x_1
-/
#guard_msgs in
set_option pp.natLit true in
#print sumSmall

/-- info: sumSmall.eq_src : ∀ (K t x x_1 : ℕ), sumSmall K t x x_1 = Src.sumSmall K t x x_1 -/
#guard_msgs in
#check @sumSmall.eq_src

/-- info: sumSmall.eq_1 : ∀ (K t x : ℕ), sumSmall K t 0 x = 0 -/
#guard_msgs in
#check @sumSmall.eq_1

/--
info: sumSmall.eq_2 : ∀ (K t x n : ℕ),
  sumSmall K t n.succ x =
    if x &&& 1 <<< K - 1 ≤ t then (x &&& 1 <<< K - 1) + sumSmall K t n (x >>> K) else sumSmall K t n (x >>> K)
-/
#guard_msgs in
#check @sumSmall.eq_2

/-- A lemma proved from the readable equations, with no recursor in sight. -/
theorem sumSmall_zero_right (K t n : ℕ) : sumSmall K t n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumSmall, ih]

/-- The slots of `0x7a3` are 3, 10 and 7; 3 and 7 are at most 9. -/
example : sumSmall 4 9 3 0x7a3 = 10 := by decide +kernel

end HandWritten

section Inline

/-- The low part of `x`, a helper written out where it is called. -/
@[kernel_inline] def low (K x : ℕ) : ℕ := x % K

/-- The high part of `x`, a helper written out where it is called. -/
@[kernel_inline] def high (K x : ℕ) : ℕ := x / K

/-- Every element of `A` has a low part below its high part, and a high part below `b`. -/
kernel_def splitsOk (K b : ℕ) (A : List ℕ) : Bool :=
  A.all fun x ↦ low K x < high K x && high K x < b

/--
info: def KernelDefTest.DocExamples.splitsOk : ℕ → ℕ → List ℕ → Bool :=
fun K b A ↦
  List.rec true (fun a x ih ↦ Bool.rec false ih (Bool.rec false ((a.div K).blt b) ((a.mod K).blt (a.div K)))) A
-/
#guard_msgs in
set_option pp.natLit true in
#print splitsOk

end Inline

section WithoutRecursion

/-- `2 ^ k − 1`, the mask of a slot of `k` bits. -/
kernel_def mask (k : ℕ) : ℕ := 1 <<< k - 1

/-- Slot `i` of `W` bits of `x`. -/
kernel_def field (W i x : ℕ) : ℕ := (x >>> (W * i)) &&& mask W

/--
info: def KernelDefTest.DocExamples.field : ℕ → ℕ → ℕ → ℕ :=
fun W i x ↦ (x.shiftRight (W.mul i)).land (mask W)
-/
#guard_msgs in
set_option pp.natLit true in
#print field

/-- info: field.eq_src : ∀ (W i x : ℕ), field W i x = Src.field W i x -/
#guard_msgs in
#check @field.eq_src

/-- info: field.eq_1 : ∀ (W i x : ℕ), field W i x = x >>> (W * i) &&& mask W -/
#guard_msgs in
#check @field.eq_1

end WithoutRecursion

section Lists

/-- The sum of a list, one `Nat.add` an element. -/
kernel_def sumL : List ℕ → ℕ
  | [] => 0
  | x :: t => x + sumL t

/--
info: def KernelDefTest.DocExamples.sumL : List ℕ → ℕ :=
fun x ↦ List.rec (nat_lit 0) (fun head tail tail_ih ↦ head.add tail_ih) x
-/
#guard_msgs in
set_option pp.natLit true in
#print sumL

/-- info: sumL.eq_1 : sumL [] = 0 -/
#guard_msgs in
#check @sumL.eq_1

/-- info: sumL.eq_2 : ∀ (x_1 : ℕ) (t : List ℕ), sumL (x_1 :: t) = x_1 + sumL t -/
#guard_msgs in
#check @sumL.eq_2

/--
info: def KernelDefTest.Shapes.allZip.{u_1, u_2} : {α : Type u_1} →
  {β : Type u_2} → (α → β → Bool) → List α → List β → Bool :=
fun {α} {β} f x x_1 ↦
  List.rec (motive := fun _ ↦ List β → Bool) (fun x ↦ List.rec true (fun head tail tail_ih ↦ false) x)
    (fun head tail tail_ih x ↦
      List.rec false (fun head_1 tail tail_ih_1 ↦ Bool.rec false (tail_ih tail) (f head head_1)) x)
    x x_1
-/
#guard_msgs in
#print KernelDefTest.Shapes.allZip

/--
info: @Shapes.allZip.eq_3 : ∀ {α : Type u_1} {β : Type u_2} (f : α → β → Bool) (x : List α) (x_1 : List β),
  (x = [] → x_1 = [] → False) →
    (∀ (a : α) (as : List α) (b : β) (bs : List β), x = a :: as → x_1 = b :: bs → False) → Shapes.allZip f x x_1 = false
-/
#guard_msgs in
#check @KernelDefTest.Shapes.allZip.eq_3

end Lists

section IntegersAndCarried

/-- A pair scaled by an integer, its sign moved into the order of the components. -/
kernel_def scale (c : ℤ) (x : ℕ × ℕ) : ℕ × ℕ :=
  match c with
  | Int.ofNat k => (k * x.fst, k * x.snd)
  | Int.negSucc k => ((k + 1) * x.snd, (k + 1) * x.fst)

/--
info: def KernelDefTest.DocExamples.scale : ℤ → ℕ × ℕ → ℕ × ℕ :=
fun c x ↦
  Int.rec (fun a ↦ (a.mul x.fst, a.mul x.snd)) (fun a ↦ ((a.add (nat_lit 1)).mul x.snd, (a.add (nat_lit 1)).mul x.fst))
    c
-/
#guard_msgs in
set_option pp.natLit true in
#print scale

/--
info: kernel audit of 1: 0 with a miss of the compiler, 1 more with a representation it keeps
misses: none
representation: pairs in 1 (4 subterms)
  scale: representation: pairs: Prod.fst ×1, Prod.mk ×2, Prod.snd ×1
-/
#guard_msgs in
#kernel_audit scale

/--
info: def KernelDefTest.Shapes.sumTo : ℕ → ℕ → ℕ :=
fun x x_1 ↦ Nat.rec (motive := fun _ ↦ ℕ → ℕ) (fun x ↦ x) (fun n n_ih x ↦ n_ih (x.add n)) x_1 x
-/
#guard_msgs in
#print KernelDefTest.Shapes.sumTo

end IntegersAndCarried

/--
info: kernel audit of 6: 0 with a miss of the compiler, 1 more with a representation it keeps
misses: none
representation: pairs in 1 (4 subterms)
  scale: representation: pairs: Prod.fst ×1, Prod.mk ×2, Prod.snd ×1
-/
#guard_msgs in
#kernel_audit sumSmall splitsOk mask field sumL scale

end KernelDefTest.DocExamples
