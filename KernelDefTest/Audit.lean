/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import KernelDef
import KernelDefTest.Accepts
import KernelDefTest.DocExamples
import KernelDefTest.Faults
import KernelDefTest.IntForms
import KernelDefTest.LibraryForms
import KernelDefTest.MathlibForms
import KernelDefTest.NatForms
import KernelDefTest.Rejects
import KernelDefTest.Shapes
import KernelDefTest.Syntax

/-!
# The audit of every kernel form

`#kernel_audit` over every kernel form of the library (`KernelDef/ListForms.lean`,
`KernelDef/NatForms.lean`, `KernelDef/IntForms.lean`, `KernelDef/MathlibForms.lean`) and of the
tests (every module of `KernelDefTest/` but this one and `Axioms.lean` is imported above). Its
line of misses must be the one that `#guard_msgs` expects: the misses of the compiler (an `ite`, a
matcher, `brecOn`, a `let`, `Decidable.decide`, an operation through an instance, a call of a
list function of the core or of a readable definition) are those that two tests make on purpose,
the `dite` and `GetElem.getElem` of `KernelDefTest.Rejects.getOr` (a proof used in the code) and
the call of `Src.total.go` in `KernelDefTest.Syn.total` (a `where` helper), and the instances of
the two library forms that are generic in a type class, by design: `KernelDef.listElem`
(`BEq.beq`, for a `[BEq α]`) and `KernelDef.listSum` (`HAdd.hAdd` and the `0` of a `[Zero α]`),
whose forms at `ℕ` (`listElemNat`, `listSumNat`) have no miss. Any other miss fails the build.
The rest of the report (the count, the representation kept: pairs, `Int`, the fields of a
structure) is not checked.

The definitions of the namespace `KernelDefTest.AuditFaults` below have misses: `#kernel_audit`
reports them, and `#kernel_audit strict` fails on them with the error that `#guard_msgs` expects.

Part of the test suite (library `KernelDefTest`); `scripts/run_tests.sh` checks that this file
imports every module of `KernelDefTest/` but itself and `Axioms.lean`.
-/

-- the line of misses that `#guard_msgs` expects is as long as Lean prints it
set_option linter.style.longLine false

/-- misses: auxiliary definition in 1 (1 subterm), dite in 1 (1 subterm), instance in 3 (4 subterms) -/
#guard_msgs (substring := true) in
#kernel_audit

namespace KernelDefTest.AuditFaults

/-- A proof used in the code: the `dite` stays. -/
kernel_def getOr (l : List ℕ) (i : ℕ) : ℕ := if h : i < l.length then l[i] else 0

/-- `max` through its instance, at `Bool`: the rule on `max` (`KernelDef/NatForms.lean`) is at
`ℕ`. -/
kernel_def maxOf (a b : Bool) : Bool := max a b

/-- A `where` helper is a second definition, called. -/
kernel_def viaWhere (n : ℕ) : ℕ := go n
where go (k : ℕ) : ℕ := k + 1

/-- Pairs and `Int`: representation, not a miss (the `+` of `ℤ` is `Int.add_k`, by the rule of
`KernelDef/IntForms.lean`). -/
kernel_def pairInt (a : ℤ) (b : ℕ) : ℤ × ℕ := (a + b, b)

/--
info: kernel audit of 4: 3 with a miss of the compiler, 1 more with a representation it keeps
misses: auxiliary definition in 1 (1 subterm), dite in 1 (1 subterm), instance in 2 (2 subterms)
representation: Int in 1 (2 subterms), pairs in 1 (1 subterm)
  getOr: misses: dite: dite ×1; instance: GetElem.getElem ×1
  maxOf: misses: instance: Max.max ×1
  viaWhere: misses: auxiliary definition: KernelDefTest.AuditFaults.Src.viaWhere.go ×1
  pairInt: representation: Int: Int.add_k ×1, Nat.cast ×1; pairs: Prod.mk ×1
-/
#guard_msgs in
#kernel_audit getOr maxOf viaWhere pairInt

/--
error: kernel audit of 1: 1 with a miss of the compiler, 0 more with a representation it keeps
misses: dite in 1 (1 subterm), instance in 1 (1 subterm)
representation: none
the misses:
  getOr: dite: dite ×1; instance: GetElem.getElem ×1
-/
#guard_msgs in
#kernel_audit strict getOr

/--
info: kernel audit of 1: 0 with a miss of the compiler, 1 more with a representation it keeps
misses: none
representation: Int in 1 (2 subterms), pairs in 1 (1 subterm)
  pairInt: representation: Int: Int.add_k ×1, Nat.cast ×1; pairs: Prod.mk ×1
-/
#guard_msgs in
#kernel_audit strict pairInt

end KernelDefTest.AuditFaults
