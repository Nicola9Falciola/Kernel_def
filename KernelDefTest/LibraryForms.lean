/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import KernelDef

/-!
# The library forms in use

A readable definition calls the functions of the core (`l.length`, `l.getD i d`, `List.range n`,
`l.foldl`, `l.sum`, `l[i]?`, `l.max?`, `a.foldl` on an array, `o.getD d`, …); with
`KernelDef/ListForms.lean` imported, its kernel form calls their kernel forms (`listLength`,
`listGetD`, `listRange'`, `listFoldl`, `listSumNat`, …) through the `@[kernel_rule]`s, and
`#kernel_audit strict` finds no miss in it. The `#guard_msgs` check the terms; the kernel decides
the `example`s through them. The forms of `ℕ`, `ℤ` and of Mathlib's functions are tested in
`NatForms.lean`, `IntForms.lean` and `MathlibForms.lean`.

Part of the test suite (library `KernelDefTest`): `lake build` fails when a message changes.
-/

namespace KernelDefTest.LibraryForms

/-- `List.length` in a source: `listLength` in the kernel form. -/
kernel_def lenPlus (l : List ℕ) (n : ℕ) : ℕ := l.length + n

/--
info: def KernelDefTest.LibraryForms.lenPlus : List ℕ → ℕ → ℕ :=
fun l n ↦ (KernelDef.listLength l).add n
-/
#guard_msgs in
#print lenPlus

/-- `List.range`, `List.map`, `List.getD` and `List.foldr` in a source. -/
kernel_def sumFirst (l : List ℕ) (k : ℕ) : ℕ :=
  ((List.range k).map fun i ↦ l.getD i 0).foldr (· + ·) 0

/--
info: def KernelDefTest.LibraryForms.sumFirst : List ℕ → ℕ → ℕ :=
fun l k ↦
  List.rec 0 (fun a x ih ↦ a.add ih)
    (List.rec [] (fun a x ih ↦ KernelDef.listGetD l a 0 :: ih) (KernelDef.listRange' 0 k 1))
-/
#guard_msgs in
#print sumFirst

/--
info: kernel audit of 2: 0 with a miss of the compiler, 0 more with a representation it keeps
misses: none
representation: none
-/
#guard_msgs in
#kernel_audit strict lenPlus sumFirst

example : lenPlus [3, 1, 4, 1, 5] 2 = 7 := by decide +kernel
example : sumFirst [3, 1, 4, 1, 5] 3 = 8 := by decide +kernel
example : sumFirst [3, 1] 4 = 4 := by decide +kernel

section Walks

/-- `List.foldl`: `listFoldl`, the accumulator carried by the recursor. -/
kernel_def foldSum (l : List ℕ) : ℕ := l.foldl (fun a x ↦ a + 2 * x) 0

/--
info: def KernelDefTest.LibraryForms.foldSum : List ℕ → ℕ :=
fun l ↦ KernelDef.listFoldl (fun a x ↦ a.add (Nat.mul 2 x)) 0 l
-/
#guard_msgs in
#print foldSum

/-- `List.sum` at `ℕ`: `listSumNat`. -/
kernel_def sumOf (l : List ℕ) : ℕ := l.sum

/--
info: def KernelDefTest.LibraryForms.sumOf : List ℕ → ℕ :=
fun l ↦ KernelDef.listSumNat l
-/
#guard_msgs in
#print sumOf

/-- `List.sum` at `ℤ`: the generic `listSum`. -/
kernel_def sumInt (l : List ℤ) : ℤ := l.sum

/-- `List.reverse` and `List.headD`. -/
kernel_def revHead (l : List ℕ) : ℕ := l.reverse.headD 0

/--
info: def KernelDefTest.LibraryForms.revHead : List ℕ → ℕ :=
fun l ↦ KernelDef.listHeadD (KernelDef.listReverseAux l []) 0
-/
#guard_msgs in
#print revHead

/-- `List.take`, `List.drop` and `++`. -/
kernel_def takeDrop (l : List ℕ) (n : ℕ) : List ℕ := l.take n ++ l.drop (n + 1)

kernel_def zipSum (l r : List ℕ) : List ℕ := List.zipWith (· + ·) l r

kernel_def flat (ls : List (List ℕ)) : List ℕ := ls.flatten

kernel_def doubled (l : List ℕ) : List ℕ := l.flatMap fun x ↦ [x, x]

example : foldSum [1, 2, 3] = 12 := by decide +kernel
example : sumOf [3, 1, 4, 1, 5] = 14 := by decide +kernel
example : sumInt [3, -1, 4] = 6 := by decide +kernel
example : revHead [3, 1, 4] = 4 := by decide +kernel
example : takeDrop [3, 1, 4, 1, 5] 2 = [3, 1, 1, 5] := by decide +kernel
example : zipSum [1, 2, 3] [10, 20] = [11, 22] := by decide +kernel
example : flat [[1, 2], [], [3]] = [1, 2, 3] := by decide +kernel
example : doubled [1, 2] = [1, 1, 2, 2] := by decide +kernel

end Walks

section Search

kernel_def getQ (l : List ℕ) (i : ℕ) : Option ℕ := l[i]?

/-- `l[i]?.getD d`: `listGetD`, by the rule declared before the one on `Option.getD`. -/
kernel_def getOr7 (l : List ℕ) (i : ℕ) : ℕ := l[i]?.getD 7

/--
info: def KernelDefTest.LibraryForms.getOr7 : List ℕ → ℕ → ℕ :=
fun l i ↦ KernelDef.listGetD l i 7
-/
#guard_msgs in
#print getOr7

/-- `l[i]!`: `listGetD`, with the default of `ℕ` a literal. -/
kernel_def getBang (l : List ℕ) (i : ℕ) : ℕ := l[i]!

/--
info: def KernelDefTest.LibraryForms.getBang : List ℕ → ℕ → ℕ :=
fun l i ↦ KernelDef.listGetD l i 0
-/
#guard_msgs in
#print getBang

kernel_def firstBig (l : List ℕ) : Option ℕ := l.find? (10 < ·)

kernel_def hasSeven (l : List ℕ) : Bool := l.elem 7

kernel_def hasSevenC (l : List ℕ) : Bool := l.contains 7

/-- `decide (a ∈ l)`: the compiler unfolds the instance to `List.elem`, and the rule at `ℕ`
fires. -/
kernel_def hasSevenM (l : List ℕ) : Bool := decide (7 ∈ l)

/--
info: def KernelDefTest.LibraryForms.hasSevenM : List ℕ → Bool :=
fun l ↦ KernelDef.listElemNat 7 l
-/
#guard_msgs in
#print hasSevenM

/-- `List.elem` at `Bool`: the generic `listElem`. -/
kernel_def hasTrue (l : List Bool) : Bool := l.elem true

kernel_def sevens (l : List ℕ) : ℕ := l.count 7

kernel_def valueOf (l : List (ℕ × ℕ)) (k : ℕ) : Option ℕ := l.lookup k

kernel_def maxOf? (l : List ℕ) : Option ℕ := l.max?

/--
info: def KernelDefTest.LibraryForms.maxOf? : List ℕ → Option ℕ :=
fun l ↦ KernelDef.listMaxNat? l
-/
#guard_msgs in
#print maxOf?

kernel_def sameList (l r : List ℕ) : Bool := decide (l = r)

kernel_def sameListB (l r : List ℕ) : Bool := l == r

example : getQ [3, 1, 4] 2 = some 4 ∧ getQ [3, 1, 4] 3 = none := by decide +kernel
example : getOr7 [3, 1, 4] 5 = 7 ∧ getOr7 [3, 1, 4] 0 = 3 := by decide +kernel
example : getBang [3, 1, 4] 1 = 1 ∧ getBang [3, 1, 4] 9 = 0 := by decide +kernel
example : firstBig [3, 12, 40] = some 12 ∧ firstBig [3] = none := by decide +kernel
example : hasSeven [3, 7] = true ∧ hasSevenC [3] = false ∧ hasSevenM [7] = true := by
  decide +kernel
example : hasTrue [false, true] = true ∧ hasTrue [false] = false := by decide +kernel
example : sevens [7, 1, 7, 7] = 3 := by decide +kernel
example : valueOf [(1, 10), (2, 20)] 2 = some 20 ∧ valueOf [(1, 10)] 2 = none := by
  decide +kernel
example : maxOf? [3, 9, 4] = some 9 ∧ maxOf? [] = none := by decide +kernel
example : sameList [1, 2] [1, 2] = true ∧ sameListB [1, 2] [1, 3] = false := by decide +kernel

end Search

section ArrayAndOption

/-- `Array.foldl`: `listFoldl` on `a.toList`, a field of the structure, which the audit lists as
representation. -/
kernel_def arrSum (a : Array ℕ) : ℕ := a.foldl (· + ·) 0

/--
info: def KernelDefTest.LibraryForms.arrSum : Array ℕ → ℕ :=
fun a ↦ KernelDef.listFoldl (fun x1 x2 ↦ x1.add x2) 0 a.toList
-/
#guard_msgs in
#print arrSum

kernel_def arrAt (a : Array ℕ) (i : ℕ) : ℕ := a[i]!

kernel_def arrSize (a : Array ℕ) : ℕ := a.size

kernel_def optOr (o : Option ℕ) : ℕ := o.getD 3

example : arrSum #[1, 2, 3, 4] = 10 := by decide +kernel
example : arrAt #[5, 6, 7] 2 = 7 ∧ arrAt #[5] 3 = 0 := by decide +kernel
example : arrSize #[5, 6, 7] = 3 := by decide +kernel
example : optOr none = 3 ∧ optOr (some 8) = 8 := by decide +kernel

end ArrayAndOption

/--
info: kernel audit of 25: 0 with a miss of the compiler, 3 more with a representation it keeps
misses: none
representation: projections in 3 (3 subterms)
  arrSum: representation: projections: Array.toList ×1
  arrAt: representation: projections: Array.toList ×1
  arrSize: representation: projections: Array.toList ×1
-/
#guard_msgs in
#kernel_audit strict foldSum sumOf sumInt revHead takeDrop zipSum flat doubled getQ getOr7 getBang
  firstBig hasSeven hasSevenC hasSevenM hasTrue sevens valueOf maxOf? sameList sameListB arrSum
  arrAt arrSize optOr

end KernelDefTest.LibraryForms
