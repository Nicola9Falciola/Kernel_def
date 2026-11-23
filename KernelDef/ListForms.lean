/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import KernelDef.KernelForm
import Mathlib.Data.Nat.Choose.Basic

/-!
# Kernel forms of the list functions of the core, arrays, `Option`, and `Nat.choose`

The kernel unfolds `List.getD` through `Option` and `GetElem`, `List.tail` and `List.headD` through
a matcher, `List.replicate`, `List.range'`, `List.eraseIdx`, `List.filter`, `++`, `List.zip`,
`List.length`, `List.foldl`, `List.reverse`, `List.take`, `List.drop`, `List.zipWith`,
`List.flatten`, `List.find?`, … through `brecOn`, the searches (`List.elem`, `List.count`,
`List.lookup`) through the instance chain of `BEq` as well, `List.max?` through a `foldl` of `max`
that the kernel evaluates superlinearly, `Array.foldl` through `Array.foldlM` with an indexed read
at every step (quadratic), and `Nat.choose` through its equation compiler. Each has here a kernel
form (a `kernel_def`), and a `@[kernel_rule]`, the equation with the function of the core, with
which the compiler writes the kernel form in its place: in every module that imports this one, a
readable definition keeps calling `l.getD i d`, and its kernel form calls `listGetD l i d`.
`List.range n` is written `listRange' 0 n 1`. What each buys: `docs/library_forms/README.md`.

A new library form follows the same pattern: a `kernel_def` in ordinary notation, then the rule
`@[kernel_rule] theorem f_eq_g : @f = g` (or an equation on applications), proved by induction.
A rule of this file is tried before the built-in rules of the compiler (`List.length` had one,
`list_length_eq_rec`, which writes the recursor in place: `listLength` names it instead).

## Order of the rules

The compiler tries the rules of a head in the order they were declared. The rules at `ℕ`
(`sum_eq_listSumNat`, `elem_eq_listElemNat`, `contains_eq_listElemNat`) come before the generic
ones (`sum_eq_listSum`, `elem_eq_listElem`, `contains_eq_listElem`), whose kernel forms keep the
instance of their class; `getElem?_getD_eq_listGetD` (section `Search`) before
`option_getD_eq_rec` (section `OptionForms`); and `foldl_eq_listFoldl` before the `kernel_def`
of `listMaxNat?`, whose source calls `List.foldl`.

## Main definitions

* `listGetD`, `listHeadD`, `listTail`, `listReplicate`, `listRange'`, `listEraseIdx`,
  `listFilter`, `listAppend`, `listZip`, `listLength`, `listFoldl`, `listSumNat`, `listSum`,
  `listReverseAux`, `listTake`, `listDrop`, `listZipWith`, `listFlatten`, `listFlatMap`,
  `listGet?`, `listFind?`, `listElemNat`, `listElem`, `listCountNat`, `listLookupNat`,
  `listMaxNat?`, `listBEqNat` — the list functions of the core, as kernel forms (an array is
  `a.toList`, and `Option.getD` a recursor, by their rules).
* `natChoose` — `Nat.choose`, by Pascal's rule, as a kernel form.

## Main results

* `getD_eq_listGetD`, `headD_eq_listHeadD`, `tail_eq_listTail`, `replicate_eq_listReplicate`,
  `range'_eq_listRange'`, `eraseIdx_eq_listEraseIdx`, `filter_eq_listFilter`,
  `append_eq_listAppend`, `zip_eq_listZip`, `range_eq_listRange'`, `length_eq_listLength`,
  `foldl_eq_listFoldl`, `sum_eq_listSumNat`, `reverse_eq_listReverseAux`, `getElem?_eq_listGet?`,
  `getElem!_eq_listGetD`, `elem_eq_listElemNat`, `max?_eq_listMaxNat?`, `decide_eq_listBEqNat`,
  `array_foldl_eq_listFoldl`, `option_getD_eq_rec`, …, `choose_eq_natChoose` — each function of
  the core is its kernel form: the 40 `@[kernel_rule]`s.

## Place in the pipeline

Imports the compiler (`KernelDef/KernelForm.lean`); `KernelDef.lean` imports both, with
`KernelDef/NatForms.lean` and `KernelDef/IntForms.lean`. The first eleven forms came from
ModularSymbolsTau, where the compiler was written (`docs/history/`).
-/

namespace KernelDef

section ListForms

variable {α : Type*}

kernel_def listGetD (l : List α) (i : ℕ) (d : α) : α :=
  match l, i with
  | [], _ => d
  | a :: _, 0 => a
  | _ :: l, i + 1 => listGetD l i d

@[kernel_rule]
theorem getD_eq_listGetD : @List.getD α = listGetD := by
  funext l i d
  induction l generalizing i with
  | nil => simp [listGetD]
  | cons a l ih =>
    cases i with
    | zero => rfl
    | succ i => simp [listGetD, ← ih]

kernel_def listHeadD : List α → α → α
  | [], d => d
  | a :: _, _ => a

@[kernel_rule]
theorem headD_eq_listHeadD : @List.headD α = listHeadD := by
  funext l d
  cases l <;> rfl

kernel_def listTail : List α → List α
  | [] => []
  | _ :: l => l

@[kernel_rule]
theorem tail_eq_listTail : @List.tail α = listTail := by
  funext l
  cases l <;> rfl

kernel_def listReplicate (n : ℕ) (a : α) : List α :=
  match n with
  | 0 => []
  | n + 1 => a :: listReplicate n a

@[kernel_rule]
theorem replicate_eq_listReplicate : @List.replicate α = listReplicate := by
  funext n a
  induction n with
  | zero => rfl
  | succ n ih => simp [listReplicate, List.replicate_succ, ih]

kernel_def listRange' (s n step : ℕ) : List ℕ :=
  match n with
  | 0 => []
  | n + 1 => s :: listRange' (s + step) n step

@[kernel_rule]
theorem range'_eq_listRange' : @List.range' = listRange' := by
  funext s n step
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [listRange', List.range'_succ, ih]

kernel_def listEraseIdx : List α → ℕ → List α
  | [], _ => []
  | _ :: l, 0 => l
  | a :: l, i + 1 => a :: listEraseIdx l i

@[kernel_rule]
theorem eraseIdx_eq_listEraseIdx : @List.eraseIdx α = listEraseIdx := by
  funext l i
  induction l generalizing i with
  | nil => simp [listEraseIdx]
  | cons a l ih => cases i <;> simp [listEraseIdx, ih]

kernel_def listFilter (p : α → Bool) : List α → List α
  | [] => []
  | a :: l => bif p a then a :: listFilter p l else listFilter p l

@[kernel_rule]
theorem filter_eq_listFilter : @List.filter α = listFilter := by
  funext p l
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [listFilter, h, ih]

kernel_def listAppend (as bs : List α) : List α :=
  match as with
  | [] => bs
  | a :: as => a :: listAppend as bs

@[kernel_rule]
theorem append_eq_listAppend (as bs : List α) : as ++ bs = listAppend as bs := by
  induction as <;> simp [listAppend, *]

kernel_def listZip {β : Type*} : List α → List β → List (α × β)
  | a :: as, b :: bs => (a, b) :: listZip as bs
  | _, _ => []

@[kernel_rule]
theorem zip_eq_listZip {β : Type*} : @List.zip α β = listZip := by
  funext as bs
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih => cases bs <;> simp [listZip, ih]

@[kernel_rule]
theorem range_eq_listRange' (n : ℕ) : List.range n = listRange' 0 n 1 := by
  rw [List.range_eq_range', range'_eq_listRange']

/-- The length of a list: a bare `List.rec` with one `Nat.add` a cons, where the kernel unfolds
`List.length` through `brecOn` and the `HAdd` instance chain. -/
kernel_def listLength : List α → ℕ
  | [] => 0
  | _ :: t => listLength t + 1

@[kernel_rule]
theorem length_eq_listLength : @List.length α = listLength := by
  funext l
  induction l with
  | nil => rfl
  | cons a l ih => simp [listLength, ih]

end ListForms

section Walks

variable {α : Type*}

/-! The folds, searches and rebuilds of a list. Each is structural recursion (`brecOn`) in the core,
and the searches go through the `BEq` instance chain (`instBEqOfDecidableEq` → `decide` →
`Nat.decEq` → `Nat.beq`); `List.max?` folds `max` through `ite`, which the kernel evaluates
superlinearly (`docs/library_forms/README.md`). The forms at `ℕ` (`listSumNat`, `listElemNat`,
`listCountNat`, `listLookupNat`, `listMaxNat?`, `listBEqNat`) call `Nat.beq` and `Nat.add`; a
generic form (`listSum`, `listElem`) keeps the instance, and its rule is declared after the rule at
`ℕ`: the compiler tries the rules of a head in the order they were declared. -/

kernel_def listFoldl {β : Type*} (f : α → β → α) : α → List β → α
  | a, [] => a
  | a, b :: l => listFoldl f (f a b) l

@[kernel_rule]
theorem foldl_eq_listFoldl {β : Type*} : @List.foldl α β = listFoldl := by
  funext f a l
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => simp [listFoldl, ih]

kernel_def listSumNat : List ℕ → ℕ
  | [] => 0
  | a :: l => a + listSumNat l

/-- `List.sum` at `ℕ`, with the instances Lean elaborates under Mathlib (`instAddNat`, and
`Zero ℕ` through `MulZeroClass.toZero`). -/
@[kernel_rule]
theorem sum_eq_listSumNat (l : List ℕ) : l.sum = listSumNat l := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [listSumNat, ih]

kernel_def listSum [Add α] [Zero α] : List α → α
  | [] => 0
  | a :: l => a + listSum l

@[kernel_rule]
theorem sum_eq_listSum [Add α] [Zero α] : @List.sum α _ _ = listSum := by
  funext l
  induction l with
  | nil => rfl
  | cons a l ih => simp [listSum, ih]

kernel_def listReverseAux : List α → List α → List α
  | [], r => r
  | a :: l, r => listReverseAux l (a :: r)

@[kernel_rule]
theorem reverseAux_eq_listReverseAux : @List.reverseAux α = listReverseAux := by
  funext l r
  induction l generalizing r with
  | nil => rfl
  | cons a l ih => simp only [List.reverseAux, listReverseAux, ih]

@[kernel_rule]
theorem reverse_eq_listReverseAux (l : List α) : l.reverse = listReverseAux l [] := by
  rw [List.reverse, reverseAux_eq_listReverseAux]

kernel_def listTake : ℕ → List α → List α
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, a :: l => a :: listTake n l

@[kernel_rule]
theorem take_eq_listTake : @List.take α = listTake := by
  funext n l
  induction n generalizing l with
  | zero => rfl
  | succ n ih => cases l <;> simp [listTake, ih]

kernel_def listDrop : ℕ → List α → List α
  | 0, l => l
  | _ + 1, [] => []
  | n + 1, _ :: l => listDrop n l

@[kernel_rule]
theorem drop_eq_listDrop : @List.drop α = listDrop := by
  funext n l
  induction n generalizing l with
  | zero => rfl
  | succ n ih => cases l <;> simp [listDrop, ih]

kernel_def listZipWith {β γ : Type*} (f : α → β → γ) : List α → List β → List γ
  | a :: as, b :: bs => f a b :: listZipWith f as bs
  | _, _ => []

@[kernel_rule]
theorem zipWith_eq_listZipWith {β γ : Type*} : @List.zipWith α β γ = listZipWith := by
  funext f as bs
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih => cases bs <;> simp [listZipWith, ih]

kernel_def listFlatten : List (List α) → List α
  | [] => []
  | l :: ls => l ++ listFlatten ls

@[kernel_rule]
theorem flatten_eq_listFlatten : @List.flatten α = listFlatten := by
  funext ls
  induction ls with
  | nil => rfl
  | cons l ls ih => simp [listFlatten, ih]

kernel_def listFlatMap {β : Type*} (f : α → List β) : List α → List β
  | [] => []
  | a :: l => f a ++ listFlatMap f l

@[kernel_rule]
theorem flatMap_eq_listFlatMap {β : Type*} : @List.flatMap α β = listFlatMap := by
  funext f l
  induction l with
  | nil => rfl
  | cons a l ih => simp [listFlatMap, ih]

end Walks

section Search

variable {α : Type*}

kernel_def listGet? : List α → ℕ → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, i + 1 => listGet? l i

@[kernel_rule]
theorem getElem?_eq_listGet? (l : List α) (i : ℕ) : l[i]? = listGet? l i := by
  induction l generalizing i with
  | nil => simp [listGet?]
  | cons a l ih => cases i <;> simp [listGet?, ih]

/-- `l[i]?.getD d` is the walk of `listGetD`, without the `Option`. Declared before the rule on
`Option.getD` (section `Option`), so that the compiler tries it first. -/
@[kernel_rule]
theorem getElem?_getD_eq_listGetD (l : List α) (i : ℕ) (d : α) :
    l[i]?.getD d = listGetD l i d := by
  rw [← List.getD_eq_getElem?_getD, getD_eq_listGetD]

@[kernel_rule]
theorem getElem!_eq_listGetD [Inhabited α] (l : List α) (i : ℕ) :
    l[i]! = listGetD l i default := by
  rw [List.getElem!_eq_getElem?_getD, getElem?_getD_eq_listGetD]

/-- The default of `ℕ`, which `l[i]!` leaves: a literal. -/
@[kernel_rule]
theorem default_eq_zero : (default : ℕ) = 0 := rfl

kernel_def listFind? (p : α → Bool) : List α → Option α
  | [] => none
  | a :: l => bif p a then some a else listFind? p l

@[kernel_rule]
theorem find?_eq_listFind? : @List.find? α = listFind? := by
  funext p l
  induction l with
  | nil => rfl
  | cons a l ih => cases h : p a <;> simp [listFind?, h, ih]

kernel_def listElemNat (a : ℕ) : List ℕ → Bool
  | [] => false
  | b :: l => a == b || listElemNat a l

kernel_def listElem [BEq α] (a : α) : List α → Bool
  | [] => false
  | b :: l => a == b || listElem a l

/-- `List.elem` at `ℕ`, with `BEq ℕ` as Lean synthesizes it (`instBEqOfDecidableEq`); also what
`decide (a ∈ l)` unfolds to. -/
@[kernel_rule]
theorem elem_eq_listElemNat (a : ℕ) (l : List ℕ) : l.elem a = listElemNat a l := by
  induction l with
  | nil => rfl
  | cons b l ih => simp only [List.elem, listElemNat, ← ih]; cases a == b <;> rfl

@[kernel_rule]
theorem elem_eq_listElem [BEq α] : @List.elem α _ = listElem := by
  funext a l
  induction l with
  | nil => rfl
  | cons b l ih => simp only [List.elem, listElem, ← ih]; cases a == b <;> rfl

@[kernel_rule]
theorem contains_eq_listElemNat (a : ℕ) (l : List ℕ) : l.contains a = listElemNat a l :=
  elem_eq_listElemNat a l

@[kernel_rule]
theorem contains_eq_listElem [BEq α] (a : α) (l : List α) : l.contains a = listElem a l := by
  rw [List.contains, elem_eq_listElem]

kernel_def listCountNat (a : ℕ) : List ℕ → ℕ
  | [] => 0
  | b :: l => bif b == a then listCountNat a l + 1 else listCountNat a l

@[kernel_rule]
theorem count_eq_listCountNat (a : ℕ) (l : List ℕ) : l.count a = listCountNat a l := by
  induction l with
  | nil => rfl
  | cons b l ih => cases h : b == a <;> simp [List.count_cons, listCountNat, h, ih]

kernel_def listLookupNat {β : Type*} (a : ℕ) : List (ℕ × β) → Option β
  | [] => none
  | (k, b) :: l => bif a == k then some b else listLookupNat a l

@[kernel_rule]
theorem lookup_eq_listLookupNat {β : Type*} (a : ℕ) (l : List (ℕ × β)) :
    l.lookup a = listLookupNat a l := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k, b⟩ := p
    cases h : a == k <;> simp [List.lookup, listLookupNat, h, ih]

/-- `List.max?` at `ℕ`: the fold of `max` written with `if`, which the compiler makes a
`Bool.rec` on `Nat.ble`; its `foldl` is `listFoldl`, by the rule above. -/
kernel_def listMaxNat? : List ℕ → Option ℕ
  | [] => none
  | a :: l => some (l.foldl (fun x y ↦ if x ≤ y then y else x) a)

@[kernel_rule]
theorem max?_eq_listMaxNat? (l : List ℕ) : l.max? = listMaxNat? l := by
  cases l with
  | nil => rfl
  | cons a l =>
    simp only [List.max?, listMaxNat?, Option.some.injEq]
    congr

kernel_def listBEqNat : List ℕ → List ℕ → Bool
  | [], [] => true
  | a :: as, b :: bs => a == b && listBEqNat as bs
  | _, _ => false

theorem listBEqNat_iff (l r : List ℕ) : listBEqNat l r = true ↔ l = r := by
  induction l generalizing r with
  | nil => cases r <;> simp [listBEqNat]
  | cons a l ih => cases r <;> simp [listBEqNat, ih]

@[kernel_rule]
theorem decide_eq_listBEqNat (l r : List ℕ) : decide (l = r) = listBEqNat l r := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, listBEqNat_iff]

@[kernel_rule]
theorem beq_eq_listBEqNat (l r : List ℕ) : (l == r) = listBEqNat l r := by
  rw [Bool.eq_iff_iff, beq_iff_eq, listBEqNat_iff]

end Search

section ArrayForms

variable {α : Type*}

/-! An array is its list `a.toList` (a structure projection, one step for the kernel). The core's
`Array.foldl` runs `Array.foldlM` in `Id`, indexing `a[j]` by a walk of `j` cells at every step:
quadratic in time and memory. -/

/-- `Array.foldl` with its default bounds (`0` and `a.size`). -/
@[kernel_rule]
theorem array_foldl_eq_listFoldl {β : Type*} (f : β → α → β) (init : β) (a : Array α) :
    a.foldl f init = listFoldl f init a.toList := by
  rw [← foldl_eq_listFoldl, Array.foldl_toList]

@[kernel_rule]
theorem array_getElem!_eq_listGetD [Inhabited α] (a : Array α) (i : ℕ) :
    a[i]! = listGetD a.toList i default := by
  rw [← getElem!_eq_listGetD]
  rcases a with ⟨l⟩
  simp

@[kernel_rule]
theorem array_size_eq (a : Array α) : a.size = a.toList.length := rfl

end ArrayForms

section OptionForms

variable {α : Type*}

/-- The general `Option.getD`, after the rule on `l[i]?.getD d` (section `Search`). -/
@[kernel_rule]
theorem option_getD_eq_rec (o : Option α) (d : α) :
    o.getD d = @Option.rec α (fun _ ↦ α) d (fun a ↦ a) o := by
  cases o <;> rfl

end OptionForms

section Choose

/-- `Nat.choose` as a kernel form: Pascal's rule, by structural recursion on `n`. -/
kernel_def natChoose : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => natChoose n k + natChoose n (k + 1)

/-- The compiler writes `natChoose` where a readable definition calls `Nat.choose`. -/
@[kernel_rule]
theorem choose_eq_natChoose : Nat.choose = natChoose := by
  funext n k
  induction n generalizing k with
  | zero => cases k <;> rfl
  | succ n ih => cases k <;> simp [natChoose, Nat.choose_succ_succ, ih]

end Choose

end KernelDef
