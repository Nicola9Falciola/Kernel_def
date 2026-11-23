/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
import Lean.Elab.Command
import Lean.Elab.PreDefinition.Basic
import Lean.Compiler.CSimpAttr
import Lean.Meta.Tactic.Delta
import Lean.Util.CollectAxioms

/-!
# Kernel forms compiled from readable definitions

## Purpose

A definition the kernel evaluates in a certificate is fast when it is written with bare recursors,
`Nat.*` heads, raw literals, `Bool.rec` on `Nat.ble` and `Nat.beq`, and no `let` (measured in
ModularSymbolsTau, `docs/CFSG_EXPERIMENTS.md`, E6–E9, E14). This file produces that form from a
definition written in ordinary notation, with a proof that the two are equal, so that the sources
hold the readable definition and the certificates evaluate the kernel form.

The compiler is not trusted. The kernel checks the equation when it is added; a definition whose
equation it rejects, whose readable definition has an error, or whose equation rests on an axiom
other than `propext`, `Classical.choice`, `Quot.sound`, is not added.

## Main definitions

* `kernel_def f …` — written as a `def`. The readable definition is `Src.f` (an ordinary `def`
  in the namespace `Src` of the current one), the kernel form is `f`, with the type of `Src.f`.
  The equations of `Src.f` are stated on `f` under the names Lean reserves for the equations of
  `f` (`f.eq_1 …`, `f.eq_def`), and `f` is marked as a recursive definition, so that `rw [f]`,
  `simp [f]` and `unfold f` read the kernel form as the readable one; `#print f` and the kernel
  see the recursors. When `Src.f` has no recursion and a `match`, the unfold equation is also
  the last of the `f.eq_i`: `simp [f]` then unfolds `f` on an argument that is not a constructor
  in form. An attribute written on a `kernel_def` is put on `f`.
* `@[kernel_inline]` — a definition the compiler unfolds where it is called: a helper worth a
  name in the source and not an unfolding in the kernel.
* `@[kernel_rule]` — an equation the compiler rewrites with, left to right.
* `#kernel_audit` — what the kernel forms still contain, in two groups: the misses of the compiler
  (an `ite`, a matcher, `brecOn`, a `let`, `Decidable.decide`, an operation through an instance, a
  call of a list function of the core or of a readable definition), and the representation it
  keeps (pairs, `Int`, the fields of a structure). `#kernel_audit strict` fails on a miss.

## What the compiler does

* Arithmetic and bit notation on `ℕ` becomes the kernel's primitive (`a + b` is `Nat.add a b`),
  and a numeral of `ℕ` a raw literal, wherever it stands.
* `a ≤ b`, `a < b`, `a = b`, `a == b` on `ℕ` become `Nat.ble`, `Nat.blt`, `Nat.beq`; `&&`, `||`,
  `!`, `if`, `bif` become `Bool.rec`; `∧`, `∨`, `¬` under an `if` likewise.
* A `let` is written out. A `match` becomes the recursor of its type.
* `List.all`, `List.any`, `List.foldr`, `List.map`, `List.length` become `List.rec`.
* Structural recursion becomes the recursor, the arguments that change in a recursive call carried
  through its motive. A recursive call is on a field of the constructor matched (the recursive
  fields are read off the recursor), or on a constructor rebuilt from the fields of a case on such
  a field (`y :: rows` after matching `x :: y :: rows`), which is the call on that field.
* Everything else is kept, its arguments compiled: pairs, projections, calls.

## Main results

* `f.eq_src : f xs = Src.f xs`, `f.src_eq : @Src.f = @f` (the rule a later definition that calls
  `Src.f` is compiled with) and `f.eq_src_fun : @f = @Src.f` (a `csimp` lemma: compiled code
  runs the readable definition, so a kernel form is computable), generated for every `kernel_def`.
* `ite_eq_boolRec`, `list_all_eq_rec`, … — the rewriting rules that are not definitional.

## Place in the pipeline

The first file of the library `KernelDef`. `KernelDef/ListForms.lean`, `NatForms.lean`,
`IntForms.lean` and the optional `MathlibForms.lean` give the library functions that readable
definitions call (`List.getD`, `List.foldl`, `Nat.log2`, `+` on `ℤ`, `Nat.choose`, …) kernel forms
and `@[kernel_rule]`s; a client imports the compiler and all but `MathlibForms` through
`KernelDef.lean`. The tests of `KernelDefTest` exercise it, and `scripts/term_gate.py` checks that
the terms it produces do not change, against `test/golden/`.
-/

namespace KernelDef

open Lean Meta Elab Command

universe u v

section Rules

theorem ite_eq_boolRec {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) :
    ite c t e = @Bool.rec (fun _ ↦ α) e t (decide c) := by
  cases h <;> rfl

theorem decide_eq_true_eq_self (b : Bool) [h : Decidable (b = true)] : decide (b = true) = b := by
  cases b <;> simp

theorem decide_and_eq_boolRec (p q : Prop) [Decidable p] [Decidable q] [h : Decidable (p ∧ q)] :
    decide (p ∧ q) = @Bool.rec (fun _ ↦ Bool) false (decide q) (decide p) := by
  by_cases hp : p <;> simp [hp]

theorem decide_or_eq_boolRec (p q : Prop) [Decidable p] [Decidable q] [h : Decidable (p ∨ q)] :
    decide (p ∨ q) = @Bool.rec (fun _ ↦ Bool) (decide q) true (decide p) := by
  by_cases hp : p <;> simp [hp]

theorem decide_not_eq_boolRec (p : Prop) [Decidable p] [h : Decidable (¬p)] :
    decide (¬p) = @Bool.rec (fun _ ↦ Bool) true false (decide p) := by
  by_cases hp : p <;> simp [hp]

theorem decide_ne_eq_boolRec {α : Sort u} (a b : α) [Decidable (a = b)] [h : Decidable (a ≠ b)] :
    decide (a ≠ b) = @Bool.rec (fun _ ↦ Bool) true false (decide (a = b)) := by
  by_cases hp : a = b <;> simp [hp]

theorem list_all_eq_rec {α : Type u} (l : List α) (p : α → Bool) :
    l.all p = @List.rec α (fun _ ↦ Bool) true
      (fun a _ ih ↦ @Bool.rec (fun _ ↦ Bool) false ih (p a)) l := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.all_cons, ih]; rfl

theorem list_any_eq_rec {α : Type u} (l : List α) (p : α → Bool) :
    l.any p = @List.rec α (fun _ ↦ Bool) false
      (fun a _ ih ↦ @Bool.rec (fun _ ↦ Bool) ih true (p a)) l := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.any_cons, ih]; rfl

theorem list_foldr_eq_rec {α : Type u} {β : Type v} (f : α → β → β) (b : β) (l : List α) :
    l.foldr f b = @List.rec α (fun _ ↦ β) b (fun a _ ih ↦ f a ih) l := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.foldr_cons, ih]

theorem list_map_eq_rec {α : Type u} {β : Type v} (f : α → β) (l : List α) :
    l.map f = @List.rec α (fun _ ↦ List β) [] (fun a _ ih ↦ f a :: ih) l := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.map_cons, ih]

theorem list_length_eq_rec {α : Type u} (l : List α) :
    l.length = @List.rec α (fun _ ↦ Nat) (nat_lit 0) (fun _ _ ih ↦ Nat.add ih (nat_lit 1)) l := by
  induction l with
  | nil => rfl
  | cons a t ih => rw [List.length_cons, ih]

end Rules

section Registry

/-- An equation `∀ xs, lhs = rhs` the compiler rewrites with: the head constant of `lhs` and its
number of arguments. -/
structure Rule where
  thm : Name
  head : Name
  arity : Nat
  deriving Inhabited

def mkRule (thm : Name) : MetaM Rule := do
  let info ← getConstInfo thm
  forallTelescope info.type fun _ body ↦ do
    let some (_, lhs, _) := body.eq?
      | throwError "kernel rule `{thm}`: not an equation"
    let .const head _ := lhs.getAppFn
      | throwError "kernel rule `{thm}`: the left side has no head constant"
    return { thm, head, arity := lhs.getAppNumArgs }

initialize ruleExt : SimpleScopedEnvExtension Rule (NameMap (Array Rule)) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun s r ↦ s.insert r.head ((s.getD r.head #[]).push r)
    initial := {}
  }

initialize registerBuiltinAttribute {
  name := `kernel_rule
  descr := "an equation the kernel-form compiler rewrites with, left to right"
  add := fun decl _ kind ↦ do
    let r ← (mkRule decl).run'
    ruleExt.add r kind
}

/-- `@[kernel_inline] def g …`: the compiler replaces a call of `g` by its body, as a notation
would. For a helper that is worth a name in the source and not an unfolding in the kernel. -/
initialize inlineAttr : TagAttribute ←
  registerTagAttribute `kernel_inline "the kernel-form compiler unfolds this definition"

/-- The readable definition a kernel form was compiled from, and the kernel form of a readable
definition. -/
structure Pair where
  src : Name
  kernel : Name
  /-- how the equation was proved: `"unfolding"` (the two sides are definitionally equal),
  `"rewriting"` (a proof term, no induction) or `"induction"` -/
  proof : String
  deriving Inhabited

initialize pairExt : SimplePersistentEnvExtension Pair (NameMap Name × NameMap Pair) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s p ↦ (s.fst.insert p.src p.kernel, s.snd.insert p.kernel p)
    addImportedFn := fun as ↦ as.foldl (fun s a ↦
      a.foldl (fun s p ↦ (s.fst.insert p.src p.kernel, s.snd.insert p.kernel p)) s) ({}, {})
  }

/-- The rules that come with the compiler. -/
def builtinRules : List Name :=
  [``ite_eq_boolRec, ``decide_eq_true_eq_self, ``decide_and_eq_boolRec, ``decide_or_eq_boolRec,
   ``decide_not_eq_boolRec, ``decide_ne_eq_boolRec, ``list_all_eq_rec, ``list_any_eq_rec,
   ``list_foldr_eq_rec, ``list_map_eq_rec, ``list_length_eq_rec]

end Registry

section Translation

/-- The recursion being compiled: the readable function at the parameters of its definition, the
position of the argument it recurses on, the positions of the arguments that change in a recursive
call, and, for each recursive field of the constructor at hand, the field, the value of the kernel
form there (the induction variable of the recursor) and the hypothesis that the readable function
equals it. -/
structure RecInfo where
  fnName : Name
  params : Array Expr
  recPos : Nat
  varying : Array Nat
  ihs : Array (Expr × Expr × Expr)

structure Context where
  rules : NameMap (Array Rule)
  recInfo? : Option RecInfo := none

abbrev M := ReaderT Context MetaM

/-- A translated term, with a proof that the term it comes from equals it; no proof when the two
are definitionally equal. -/
structure Res where
  expr : Expr
  proof? : Option Expr := none
  deriving Inhabited

def Res.trans (r₁ r₂ : Res) : MetaM Res :=
  match r₁.proof?, r₂.proof? with
  | some p, some q => return { expr := r₂.expr, proof? := some (← mkEqTrans p q) }
  | some p, none => return { expr := r₂.expr, proof? := some p }
  | none, q? => return { expr := r₂.expr, proof? := q? }

/-- The arithmetic notations on `ℕ` and the kernel's primitive behind each. -/
def natNotation : List (Name × Name) :=
  [(``HAdd.hAdd, ``Nat.add), (``HSub.hSub, ``Nat.sub), (``HMul.hMul, ``Nat.mul),
   (``HDiv.hDiv, ``Nat.div), (``HMod.hMod, ``Nat.mod), (``HPow.hPow, ``Nat.pow),
   (``HAnd.hAnd, ``Nat.land), (``HOr.hOr, ``Nat.lor), (``HXor.hXor, ``Nat.xor),
   (``HShiftLeft.hShiftLeft, ``Nat.shiftLeft), (``HShiftRight.hShiftRight, ``Nat.shiftRight)]

def natOp? (e : Expr) : Option (Name × Expr × Expr) :=
  match e.getAppFn with
  | .const c _ =>
    let args := e.getAppArgs
    if args.size == 6 && args[0]!.isConstOf ``Nat && args[1]!.isConstOf ``Nat &&
        args[2]!.isConstOf ``Nat then
      (natNotation.lookup c).map fun p ↦ (p, args[4]!, args[5]!)
    else none
  | _ => none

/-- A numeral of `ℕ` as the elaborator writes it, `OfNat.ofNat ℕ n _`. Its type carries a
metadata node when the numeral is an argument of a primitive. -/
def isNatNumeral (e : Expr) : Bool :=
  e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 0).consumeMData.isConstOf ``Nat &&
    (e.getArg! 1).isRawNatLit

/-- `a < b` on `ℕ`, also written `b > a`. -/
def natLt? (p : Expr) : MetaM (Option (Expr × Expr)) := do
  let p ← whnfR p
  if p.isAppOfArity ``LT.lt 4 && (p.getArg! 0).isConstOf ``Nat then
    return some (p.getArg! 2, p.getArg! 3)
  return none

/-- The definitions the compiler always unfolds: each is a `Bool.rec` after one or two steps. -/
def unfolded : List Name := [``Bool.and, ``Bool.or, ``Bool.not, ``cond, ``bne, ``Bool.xor]

/-- `e` with its head β-reduced until it is no redex. -/
partial def headBetaAll (e : Expr) : Expr :=
  if e.isHeadBetaTarget then headBetaAll e.headBeta else e

def isSparseCasesOn (n : Name) : Bool :=
  match n with
  | .str _ s => s.startsWith "_sparseCasesOn_"
  | _ => false

/-- `e` with its head constant unfolded and every β-redex this leaves reduced (the binder types
of an unfolded `casesOn` or `match` hold redexes of the motive). -/
def unfold? (e : Expr) : MetaM (Option Expr) := do
  let some e ← delta? e | return none
  return some (← Core.betaReduce e)

/-- `f a₁ … aₙ` with some arguments replaced by their translations. -/
def congrApp (f : Expr) (args : Array Expr) (rs : Array (Option Res)) : MetaM Res := do
  let mut cur := args
  let mut proof? : Option Expr := none
  for i in [:args.size] do
    let some r := rs[i]! | continue
    match r.proof? with
    | none => cur := cur.set! i r.expr
    | some p =>
      let ctx ← withLocalDeclD `z (← inferType args[i]!) fun z ↦
        mkLambdaFVars #[z] (mkAppN f (cur.set! i z))
      let step ← mkCongrArg ctx p
      cur := cur.set! i r.expr
      proof? := some (← match proof? with
        | none => pure step
        | some q => mkEqTrans q step)
  return { expr := mkAppN f cur, proof? }

def mkFunExts (xs : Array Expr) (p : Expr) : MetaM Expr :=
  xs.foldrM (fun x p ↦ do mkFunExt (← mkLambdaFVars #[x] p)) p

/-- The equation `rule` at `e`: its right side and the proof. -/
def applyRule? (rule : Rule) (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let info ← getConstInfo rule.thm
  let us ← info.levelParams.mapM fun _ ↦ mkFreshLevelMVar
  let (ms, bis, eqn) ← forallMetaTelescope (info.type.instantiateLevelParams info.levelParams us)
  let some (_, lhs, rhs) := eqn.eq? | return none
  unless ← withReducible (isDefEq lhs e) do return none
  for m in ms, bi in bis do
    if bi.isInstImplicit && !(← m.mvarId!.isAssigned) then
      let some inst ← synthInstance? (← inferType m) | return none
      m.mvarId!.assign inst
  let rhs ← instantiateMVars rhs
  let prf ← instantiateMVars (mkAppN (mkConst rule.thm us) ms)
  if rhs.hasMVar || prf.hasMVar then return none
  return some (rhs, prf)

/-- The applications of `fn` in `e`. -/
partial def recCalls (fn : Name) (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  match e with
  | .app .. =>
    let acc := e.getAppArgs.foldl (fun acc a ↦ recCalls fn a acc) acc
    if e.getAppFn.isConstOf fn then acc.push e else recCalls fn e.getAppFn acc
  | .lam _ d b _ | .forallE _ d b _ => recCalls fn b (recCalls fn d acc)
  | .letE _ t v b _ => recCalls fn b (recCalls fn v (recCalls fn t acc))
  | .mdata _ b | .proj _ _ b => recCalls fn b acc
  | _ => acc

/-- The inductive type of `y` (no indices), its universe levels and its parameters. -/
def inductiveOf (y : Expr) : MetaM (InductiveVal × List Level × Array Expr × Expr) := do
  let yT ← whnf (← inferType y)
  let .const I lvls := yT.getAppFn
    | throwError "kernel form: {y} is not in an inductive type"
  let ind ← getConstInfoInduct I
  unless ind.numIndices == 0 do
    throwError "kernel form: the inductive type `{I}` has indices"
  return (ind, lvls, yT.getAppArgs, yT)

/-- The types of the minor premises of a recursor applied to its parameters and motive. -/
def minorTypes (recFn : Expr) (n : Nat) : MetaM (Array Expr) := do
  let mut ty ← inferType recFn
  let mut out := #[]
  for _ in [:n] do
    let .forallE _ d b _ ← whnf ty | throwError "kernel form: unexpected recursor type"
    if b.hasLooseBVars then throwError "kernel form: dependent minor premises"
    out := out.push d
    ty := b
  return out

/-- For each constructor of the inductive type `yT`, the positions of its recursive fields, in the
order of the induction hypotheses of the recursor's minor premise: the field each hypothesis is
about. They are read off the recursor at a motive that is a variable, not off the types of the
fields, which may be an `abbrev` of the type itself (the head of a cons in `List (SRow ℤ)`). -/
def recFieldPositions (ind : InductiveVal) (lvls : List Level) (params : Array Expr)
    (yT : Expr) : MetaM (Array (Array Nat)) := do
  withLocalDeclD `motive (← mkArrow yT (mkSort Level.one)) fun m ↦ do
    let recFn := mkAppN (mkConst (mkRecName ind.name) (Level.one :: lvls)) (params.push m)
    let mTypes ← minorTypes recFn ind.numCtors
    let mut out := #[]
    for ctor in ind.ctors, mType in mTypes do
      let cv ← getConstInfoCtor ctor
      let pos ← forallBoundedTelescope mType cv.numFields fun fields rest ↦
        forallTelescope rest fun ihs _ ↦ ihs.mapM fun ih ↦ do
          forallTelescope (← inferType ih) fun _ b ↦ do
            let some i := fields.findIdx? (· == b.appArg!.getAppFn)
              | throwError "kernel form: an induction hypothesis of `{ctor}` on no field"
            return i
      out := out.push pos
    return out

/-- Whether `e` calls the function being compiled on something other than a field of the
constructor at hand: on a constructor rebuilt from the fields of a case, say. -/
def callsOnRebuilt (ri : RecInfo) (e : Expr) : Bool :=
  (recCalls ri.fnName e).any fun c ↦ !ri.ihs.any (·.fst == c.getArg! ri.recPos)

mutual

/-- The kernel form of `e`. -/
partial def tr (e : Expr) : M Res := do
  match e with
  | .mdata _ b => tr b
  | .letE _ _ v b _ => tr (b.instantiate1 v)
  | .lam .. =>
    lambdaTelescope e fun xs b ↦ do
      let r ← tr b
      let expr ← mkLambdaFVars xs r.expr
      match r.proof? with
      | none => return { expr }
      | some p => return { expr, proof? := some (← mkFunExts xs p) }
  | .proj _ _ b =>
    let r ← tr b
    match r.proof? with
    | none => return { expr := e.updateProj! r.expr }
    | some p =>
      let ctx ← withLocalDeclD `z (← inferType b) fun z ↦ mkLambdaFVars #[z] (e.updateProj! z)
      return { expr := e.updateProj! r.expr, proof? := some (← mkCongrArg ctx p) }
  | .const c _ =>
    if c == ``Nat.zero then return { expr := mkRawNatLit 0 }
    match ← applyRules? e with
    | some r => return r
    | none => return { expr := e }
  | .app .. => trApp (headBetaAll e)
  | _ => return { expr := e }

partial def trApp (e : Expr) : M Res := do
  unless e.isApp do return ← tr e
  let fn := e.getAppFn
  let args := e.getAppArgs
  if isNatNumeral e then return { expr := args[1]! }
  if let some (op, a, b) := natOp? e then return ← trPrim op a b
  let .const c _ := fn | trGeneric e
  if c == ``Decidable.decide && args.size == 2 then return ← trDecide e
  if c == ``BEq.beq && args.size == 4 && args[0]!.isConstOf ``Nat then
    return ← trPrim ``Nat.beq args[2]! args[3]!
  if unfolded.contains c || inlineAttr.hasTag (← getEnv) c then
    if let some e' ← unfold? e then return ← tr e'
  if ← isMatcher c then return ← trMatcher e
  if isCasesOnRecursor (← getEnv) c then
    if let some e' ← unfold? e then return ← tr e'
  if (← getConstInfo c) matches .recInfo .. then return ← trRec e
  if let some ri := (← read).recInfo? then
    if c == ri.fnName then return ← trRecCall ri e
  if let some r ← applyRules? e then return r
  trGeneric e

/-- The primitive `op` at the kernel forms of `a` and `b`: what a notation on `ℕ` becomes. -/
partial def trPrim (op : Name) (a b : Expr) : M Res := do
  congrApp (mkConst op) #[a, b] #[some (← tr a), some (← tr b)]

/-- A test `decide p`: by a rule, or the Boolean the instance holds. -/
partial def trDecide (e : Expr) : M Res := do
  let p := e.getArg! 0
  if let some (a, b) ← natLt? p then return ← trPrim ``Nat.blt a b
  if let some r ← applyRules? e then return r
  let inst ← withTransparency .instances (whnf (e.getArg! 1))
  if inst.isAppOfArity ``Decidable.intro 3 then return ← tr (inst.getArg! 1)
  trGeneric e

/-- An application of a constant the compiler knows nothing about: its arguments. -/
partial def trGeneric (e : Expr) : M Res := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  let finfo ← getFunInfoNArgs fn args.size
  let mut rs := #[]
  for i in [:args.size] do
    let a := args[i]!
    let skip ← if h : i < finfo.paramInfo.size then
        let pi := finfo.paramInfo[i]
        pure (pi.isInstImplicit || pi.isProp || pi.hasFwdDeps)
      else isProof a
    if skip then rs := rs.push none else rs := rs.push (some (← tr a))
  congrApp fn args rs

/-- `pre rest`, where `pre` has been rewritten as `r`: the rest of the arguments, then on. -/
partial def appRest (r : Res) (rest : Array Expr) : M Res := do
  let proof? ← r.proof?.mapM fun p ↦ rest.foldlM (fun p a ↦ mkCongrFun p a) p
  let r₂ ← tr (headBetaAll (mkAppN r.expr rest))
  Res.trans { expr := r.expr, proof? } r₂

partial def applyRules? (e : Expr) : M (Option Res) := do
  let .const c _ := e.getAppFn | return none
  let some rules := (← read).rules.find? c | return none
  let args := e.getAppArgs
  for rule in rules do
    if rule.arity > args.size then continue
    let pre := mkAppN e.getAppFn (args.extract 0 rule.arity)
    if let some (rhs, prf) ← applyRule? rule pre then
      return some (← appRest { expr := rhs, proof? := some prf } (args.extract rule.arity))
  return none

/-- A recursor with a constant motive: its minor premises, its major premise and the arguments
after it. -/
partial def trRec (e : Expr) : M Res := do
  let .const c _ := e.getAppFn | trGeneric e
  let .recInfo rv ← getConstInfo c | trGeneric e
  let args := e.getAppArgs
  unless rv.numMotives == 1 && rv.numIndices == 0 && args.size > rv.getMajorIdx do
    return { expr := e }
  -- a recursor on a constructor (a `match` on a variable replaced by one): its value
  let major := args[rv.getMajorIdx]!
  if major.isRawNatLit || (← isConstructorApp major) then
    let e' ← whnfCore e
    if e' != e then return ← tr (← Core.betaReduce e')
  let motive := args[rv.numParams]!
  unless motive.isLambda && !motive.bindingBody!.hasLooseBVars do return { expr := e }
  -- a recursor on a recursive field, under which the function is called on a constructor rebuilt
  -- from the fields of a case: by cases, the hypothesis on the field carried into each
  if let some ri := (← read).recInfo? then
    if major.isFVar && ri.ihs.any (·.fst == major) && callsOnRebuilt ri e then
      return ← splitOn major e
  let mut rs := #[]
  for i in [:args.size] do
    if i ≤ rv.numParams then rs := rs.push none else rs := rs.push (some (← tr args[i]!))
  congrApp e.getAppFn args rs

/-- A call of the function being compiled, on a field of the constructor at hand (or on a
constructor rebuilt from the fields of a case on that field): the induction variable of the
recursor at the arguments that change. -/
partial def trRecCall (ri : RecInfo) (e : Expr) : M Res := do
  let args := e.getAppArgs
  let n := ri.params.size
  if args.size < n then
    throwError "kernel form: a recursive call with too few arguments{indentExpr e}"
  -- a rebuilt constructor may be written otherwise (`n + 1` for `Nat.succ n`)
  let arg := args[ri.recPos]!
  let some (_, g, h) ← ri.ihs.findM? fun (k, _, _) ↦
      return k == arg || (!k.isFVar && (← isDefEq k arg))
    | throwError "kernel form: the recursive call{indentExpr e}\nis not on a field of the \
        constructor matched"
  let mut rs := #[]
  for i in [:n] do
    if ri.varying.contains i then rs := rs.push (some (← tr args[i]!)) else rs := rs.push none
  let r₁ ← congrApp e.getAppFn (args.extract 0 n) rs
  let ws := ri.varying.map fun i ↦ (rs[i]!.get!).expr
  let r₂ ← Res.trans r₁ { expr := mkAppN g ws, proof? := some (mkAppN h ws) }
  appRest r₂ (args.extract n)

/-- The variable a `match` waits for: the major premise of the recursor it is stuck on. -/
partial def stuckMajor? (e : Expr) : M (Option Expr) := do
  let some e ← delta? e | return none
  let e ← whnfCore (headBetaAll e)
  let .const c _ := e.getAppFn | return none
  match ← getConstInfo c with
  | .recInfo rv => return e.getAppArgs[rv.getMajorIdx]?
  | .defnInfo _ =>
    if isCasesOnRecursor (← getEnv) c || isSparseCasesOn c || (← isMatcher c) then
      stuckMajor? e
    else return none
  | _ => return none

/-- A `match`. One that reduces is replaced by its value. One that unfolds to a chain of `casesOn`
is that chain. Otherwise (overlapping patterns) the term is split on the variable the match waits
for, and the equation is proved by cases. -/
partial def trMatcher (e : Expr) : M Res := do
  match ← reduceMatcher? e with
  | .reduced e' => return ← tr (headBetaAll e')
  | .stuck _ =>
    let some e' ← unfold? e | trGeneric e
    if (e'.find? fun s ↦ s.isConst && isSparseCasesOn s.constName!).isNone then
      return ← tr e'
    let some major ← stuckMajor? e
      | throwError "kernel form: cannot compile the match{indentExpr e}"
    if major.isFVar then return ← splitOn major e
    let abs ← kabstract e major
    unless abs.hasLooseBVars do
      throwError "kernel form: cannot compile the match{indentExpr e}"
    withLocalDeclD `y (← inferType major) fun y ↦ do
      let r ← splitOn y (abs.instantiate1 y)
      let rm ← tr major
      let fn ← mkLambdaFVars #[y] r.expr
      let p₁? ← r.proof?.mapM fun p ↦ return (← mkLambdaFVars #[y] p).beta #[major]
      let p₂? ← rm.proof?.mapM fun q ↦ mkCongrArg fn q
      Res.trans { expr := fn.beta #[major], proof? := p₁? }
        { expr := fn.beta #[rm.expr], proof? := p₂? }
  | _ => trGeneric e

/-- `e` by cases on the variable `y`: a recursor on `y` whose minor premise at a constructor is
the kernel form of `e` with `y` replaced by that constructor. When `y` is a recursive field of the
constructor matched by the recursion, its hypothesis `h` is carried into each case, at the
constructor `c zs` of the case: a recursive call on `c zs` (`y :: rows` after matching
`x :: y :: rows`) is then a call on `y`. -/
partial def splitOn (y e : Expr) : M Res := do
  let (ind, lvls, params, yT) ← inductiveOf y
  let T ← instantiateMVars (← inferType e)
  let motive := mkLambda `_ .default yT T
  let recFn := mkAppN (mkConst (mkRecName ind.name) ((← getLevel T) :: lvls)) (params.push motive)
  let mTypes ← minorTypes recFn ind.numCtors
  let recFieldPos ← recFieldPositions ind lvls params yT
  let ih? := (← read).recInfo?.bind fun ri ↦ ri.ihs.find? (·.fst == y)
  let hType? ← ih?.mapM fun (_, _, h) ↦ inferType h
  let mut minors := #[]
  let mut proofs := #[]
  for ctor in ind.ctors, mType in mTypes, pos in recFieldPos do
    let cv ← getConstInfoCtor ctor
    let (minor, proof) ← forallBoundedTelescope mType cv.numFields fun fields rest ↦ do
      let val := mkAppN (mkConst ctor lvls) (params ++ fields)
      let case (hs : Array Expr) : M (Expr × Expr) := do
        let r ← tr (e.replaceFVar y val)
        let minor ← forallBoundedTelescope rest pos.size fun ihs _ ↦
          mkLambdaFVars (fields ++ ihs) r.expr
        let p ← match r.proof? with
          | some p => pure p
          | none => mkEqRefl r.expr
        return (minor, ← mkLambdaFVars (fields ++ hs) p)
      match ih?, hType? with
      | some (_, g, _), some t =>
        withLocalDeclD `h (t.replaceFVar y val) fun h' ↦
          withReader (fun ctx ↦ { ctx with recInfo? := ctx.recInfo?.map fun ri ↦
            { ri with ihs := ri.ihs.push (val, g, h') } }) (case #[h'])
      | _, _ => case #[]
    minors := minors.push minor
    proofs := proofs.push proof
  let recApp := mkAppN recFn minors
  let goal (v : Expr) : MetaM Expr := do
    let eq ← mkEq (e.replaceFVar y v) (mkApp recApp v)
    match hType? with
    | some t => mkArrow (t.replaceFVar y v) eq
    | none => pure eq
  let pmotive ← mkLambdaFVars #[y] (← goal y)
  let casesFn := mkAppN (mkConst (mkCasesOnName ind.name) (Level.zero :: lvls))
    (params ++ #[pmotive, y])
  let mut pminors := #[]
  for ctor in ind.ctors, proof in proofs do
    let cv ← getConstInfoCtor ctor
    let pminor ← lambdaBoundedTelescope proof (cv.numFields + hType?.toArray.size) fun zs p ↦ do
      let val := mkAppN (mkConst ctor lvls) (params ++ zs.extract 0 cv.numFields)
      let ty ← mkEq (e.replaceFVar y val) (mkApp recApp val)
      mkLambdaFVars zs (← mkExpectedTypeHint p ty)
    pminors := pminors.push pminor
  let prf := mkAppN casesFn pminors
  return { expr := mkApp recApp y, proof? := some (ih?.elim prf fun (_, _, h) ↦ mkApp prf h) }

end

end Translation

section Compiler

/-- The declarations a compiled definition may rest on. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def mkContext : MetaM Context := do
  let mut rules := ruleExt.getState (← getEnv)
  for n in builtinRules do
    let r ← mkRule n
    rules := rules.insert r.head ((rules.getD r.head #[]).push r)
  return { rules }

def addThm (name : Name) (levelParams : List Name) (type value : Expr) : MetaM Unit := do
  addDecl <| .thmDecl { name, levelParams, type, value }
  let axs ← collectAxioms name
  if let some a := axs.find? (!allowedAxioms.contains ·) then
    throwError "kernel form: `{name}` rests on the axiom `{a}`"

/-- The kernel form `dst` of the definition `src`, with `dst.eq_src : dst xs = src xs` and
`dst.src_eq : @src = @dst`. -/
def compile (src dst : Name) : MetaM Unit := do
  let info ← getConstInfoDefn src
  let lvls := info.levelParams.map mkLevelParam
  let srcC := mkConst src lvls
  let dstC := mkConst dst lvls
  let some eqDef ← getUnfoldEqnFor? src (nonRec := true)
    | throwError "kernel form: no unfold equation for `{src}`"
  let ctx ← mkContext
  let eqType ← inferType (mkConst eqDef lvls)
  let (pointwise, kind) ← forallTelescope eqType fun xs eqn ↦ do
    let some (R, lhs, body) := eqn.eq?
      | throwError "kernel form: unexpected unfold equation for `{src}`"
    let calls := recCalls src body
    let addDef (value : Expr) : MetaM Unit := do
      let value := ShareCommon.shareCommon' (← instantiateMVars (← mkLambdaFVars xs value))
      if (value.find? (·.isConstOf src)).isSome then
        throwError "kernel form: `{src}` is used other than in a call on a field of the \
          constructor matched"
      addDecl <| .defnDecl {
        name := dst, levelParams := info.levelParams, type := info.type, value
        hints := .regular (getMaxHeight (← getEnv) value + 1), safety := .safe }
      if isNoncomputable (← getEnv) src then modifyEnv (addNoncomputable · dst)
    if calls.isEmpty then
      let r ← (tr body).run ctx
      addDef r.expr
      let p₀ := mkAppN (mkConst eqDef lvls) xs
      let p ← match r.proof? with
        | none => pure p₀
        | some q => mkEqTrans p₀ q
      return (← mkLambdaFVars xs (← mkExpectedTypeHint p (← mkEq lhs (mkAppN dstC xs))),
        if r.proof?.isNone then "unfolding" else "rewriting")
    else
      let some recPos ← getStructuralRecArgPos? src
        | throwError "kernel form: `{src}` is not defined by structural recursion"
      for c in calls do
        unless c.getAppNumArgs ≥ xs.size do
          throwError "kernel form: a recursive call with too few arguments{indentExpr c}"
      let varying := (Array.range xs.size).filter fun i ↦
        i != recPos && calls.any fun c ↦ c.getArg! i != xs[i]!
      let y := xs[recPos]!
      let vs := varying.map (xs[·]!)
      let (ind, ilvls, params, yT) ← inductiveOf y
      let carried ← mkForallFVars vs R
      if carried.containsFVar y.fvarId! then
        throwError "kernel form: the type of `{src}` depends on the argument it recurses on"
      let motive := mkLambda `_ .default yT carried
      let recFn := mkAppN (mkConst (mkRecName ind.name) ((← getLevel carried) :: ilvls))
        (params.push motive)
      let mTypes ← minorTypes recFn ind.numCtors
      let recFieldPos ← recFieldPositions ind ilvls params yT
      let mut minors := #[]
      let mut pdatas := #[]
      for ctor in ind.ctors, mType in mTypes, pos in recFieldPos do
        let cv ← getConstInfoCtor ctor
        let (minor, pdata) ← forallBoundedTelescope mType cv.numFields fun fields rest ↦ do
          let recFields := pos.map (fields[·]!)
          forallBoundedTelescope rest recFields.size fun ihs _ ↦ do
            let hTypes ← (recFields.zip ihs).mapM fun (fld, ih) ↦ do
              mkForallFVars vs (← mkEq (mkAppN srcC (xs.set! recPos fld)) (mkAppN ih vs))
            withLocalDeclsDND (hTypes.map fun t ↦ (`h, t)) fun hs ↦ do
              let ri : RecInfo := {
                fnName := src, params := xs, recPos, varying
                ihs := recFields.zip (ihs.zip hs) }
              let val := mkAppN (mkConst ctor ilvls) (params ++ fields)
              let r ← (tr (body.replaceFVar y val)).run { ctx with recInfo? := some ri }
              let p ← match r.proof? with
                | some p => pure p
                | none => mkEqRefl r.expr
              return (← mkLambdaFVars (fields ++ ihs ++ vs) r.expr,
                ← mkLambdaFVars (fields ++ ihs ++ hs ++ vs) p)
        minors := minors.push minor
        pdatas := pdatas.push pdata
      addDef (mkAppN recFn (minors ++ #[y] ++ vs))
      let pmotive ← mkLambdaFVars #[y] (← mkForallFVars vs (← mkEq lhs (mkAppN dstC xs)))
      let precFn := mkAppN (mkConst (mkRecName ind.name) (Level.zero :: ilvls))
        (params.push pmotive)
      let pTypes ← minorTypes precFn ind.numCtors
      let mut pminors := #[]
      for ctor in ind.ctors, pType in pTypes, pdata in pdatas, pos in recFieldPos do
        let cv ← getConstInfoCtor ctor
        let pminor ← forallBoundedTelescope pType cv.numFields fun fields rest ↦ do
          let recFields := pos.map (fields[·]!)
          forallBoundedTelescope rest recFields.size fun IHs _ ↦ do
            let val := mkAppN (mkConst ctor ilvls) (params ++ fields)
            let gs ← recFields.mapM fun fld ↦
              mkLambdaFVars vs (mkAppN dstC (xs.set! recPos fld))
            let p := pdata.beta (fields ++ gs ++ IHs ++ vs)
            let p₀ := mkAppN (mkConst eqDef lvls) (xs.set! recPos val)
            let ty ← mkEq (mkAppN srcC (xs.set! recPos val)) (mkAppN dstC (xs.set! recPos val))
            mkLambdaFVars (fields ++ IHs ++ vs) (← mkExpectedTypeHint (← mkEqTrans p₀ p) ty)
        pminors := pminors.push pminor
      return (← mkLambdaFVars xs (mkAppN precFn (pminors ++ #[y] ++ vs)), "induction")
  let pointwise ← instantiateMVars pointwise
  -- `dst xs = src xs`, then `@src = @dst`
  let (eqSrcType, eqSrcVal, funType, funVal) ← forallTelescope eqType fun xs eqn ↦ do
    let some (_, lhs, _) := eqn.eq? | unreachable!
    let p := mkAppN pointwise xs
    let rhs := mkAppN dstC xs
    return (← mkForallFVars xs (← mkEq rhs lhs), ← mkLambdaFVars xs (← mkEqSymm p),
      ← mkEq srcC dstC, ← mkFunExts xs (← mkExpectedTypeHint p (← mkEq lhs rhs)))
  addThm (dst ++ `eq_src) info.levelParams eqSrcType eqSrcVal
  addThm (dst ++ `src_eq) info.levelParams funType funVal
  -- compiled code runs the readable definition
  addThm (dst ++ `eq_src_fun) info.levelParams (← mkEq dstC srcC)
    (← mkEqSymm (mkConst (dst ++ `src_eq) lvls))
  unless isNoncomputable (← getEnv) src do
    Compiler.CSimp.add (dst ++ `eq_src_fun) .global
  ruleExt.add { thm := dst ++ `src_eq, head := src, arity := 0 }
  modifyEnv (pairExt.addEntry · { src, kernel := dst, proof := kind })
  if let some doc ← findDocString? (← getEnv) src then
    addDocStringCore dst doc

/-- The statement `stmt` with every readable definition replaced by its kernel form, and a proof
that the two statements are equal. -/
def toKernelStmt (stmt : Expr) : MetaM (Expr × Option Expr) := do
  let srcs := (pairExt.getState (← getEnv)).fst
  let consts := (stmt.foldConsts #[] fun n acc ↦ if srcs.contains n then acc.push n else acc)
  let mut stmt := stmt
  let mut proof? : Option Expr := none
  for n in consts do
    let some k := srcs.find? n | continue
    let some c := stmt.find? (·.isConstOf n) | continue
    let us := c.constLevels!
    let h := mkConst (k ++ `src_eq) us
    let cur := stmt
    let ctx ← withLocalDeclD `F (← inferType c) fun F ↦
      mkLambdaFVars #[F] (cur.replace fun e ↦ if e == c then some F else none)
    let step ← mkCongrArg ctx h
    stmt := stmt.replace fun e ↦ if e == c then some (mkConst k us) else none
    proof? := some (← match proof? with
      | none => pure step
      | some q => mkEqTrans q step)
  return (stmt, proof?)

/-- The equations of the readable definition `src`, stated on its kernel form `dst` under the
names Lean reserves for the equations of `dst`: `rw [dst]` and `simp [dst]` then use them. -/
def addEquations (src dst : Name) : MetaM Unit := do
  let add (thm name : Name) : MetaM Unit := do
    let info ← getConstInfo thm
    let (type, proof?) ← toKernelStmt info.type
    let lvls := info.levelParams.map mkLevelParam
    let value ← match proof? with
      | none => pure (mkConst thm lvls)
      | some p => mkEqMP p (mkConst thm lvls)
    addThm name info.levelParams type value
  let eqDef? ← getUnfoldEqnFor? src (nonRec := true)
  if let some eqns ← getEqnsFor? src then
    for eqn in eqns, i in [1:eqns.size + 1] do
      add eqn (dst ++ Name.mkSimple s!"eq_{i}")
    -- A definition without recursion whose `match` gives several equations: the unfold equation
    -- comes last, so that `simp [dst]` still unfolds `dst c` when `c` is no constructor in
    -- form (a cast, a numeral) and reduces the `match` itself, as it does for a plain `def`.
    if let some eqDef := eqDef? then
      if eqns.size > 1 && !(← isRecursiveDefinition src) then
        add eqDef (dst ++ Name.mkSimple s!"eq_{eqns.size + 1}")
  if let some eqDef := eqDef? then
    add eqDef (dst ++ `eq_def)
  -- `simp [dst]` then rewrites with these equations and does not unfold `dst` to its recursors
  markAsRecursive dst

end Compiler

section Audit

/-- The primitives the kernel runs on literals, and `Nat.blt`, which the compiler writes for `<`
(one unfolding to `Nat.ble`). `Nat.log2` is not among them: the kernel of Lean `v4.37.0-rc1` runs
its definition, one step a bit of the argument (`KernelDef/NatForms.lean` has its kernel form). -/
def kernelNatOps : List Name :=
  [``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.pow, ``Nat.gcd, ``Nat.beq,
   ``Nat.ble, ``Nat.blt, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight]

/-- Something a kernel form still contains: a miss of the compiler (`miss`), which should not be
there, or a representation it keeps (pairs, `Int`, the fields of a structure); its category, and
the constant. -/
structure Finding where
  miss : Bool
  category : String
  what : Name
  deriving BEq, Hashable, Inhabited

/-- The roots of the modules of the user's code: those of the modules that hold a kernel form,
and that of the present module. -/
def userRoots (env : Environment) : NameSet :=
  (pairExt.getState env).snd.foldl (init := NameSet.empty.insert env.mainModule.getRoot)
    fun s k _ ↦ match env.getModuleIdxFor? k with
      | some i => s.insert env.header.moduleNames[i.toNat]!.getRoot
      | none => s

/-- A definition of a library (the core, Mathlib, …): one of a module whose root is not among
`roots`, the roots of the user's code (`userRoots`). -/
def isLibraryConst (env : Environment) (roots : NameSet) (c : Name) : Bool :=
  match env.getModuleIdxFor? c with
  | none => false
  | some i => !roots.contains env.header.moduleNames[i.toNat]!.getRoot

def isIntType (e : Option Expr) : Bool := e.any (·.consumeMData.isConstOf ``Int)

/-- What the head `c` of an application to `args` is, if it is something to report, and how many
of the first arguments not to look into (the proposition and the instance of an `if`, the types
and the instance of an operation through an instance). `roots` are the roots of the modules of
the user's code (`userRoots`). -/
def classifyHead (roots : NameSet) (c : Name) (args : Array Expr) :
    MetaM (Option Finding × Nat) := do
  let env ← getEnv
  let miss (category : String) : Option Finding := some { miss := true, category, what := c }
  let repr (category : String) : Option Finding := some { miss := false, category, what := c }
  if c == ``ite then return (miss "ite", 3)
  if c == ``dite then return (miss "dite", 3)
  if c == ``Decidable.decide then return (miss "decide", args.size)
  if c == ``Decidable.rec || c == ``Decidable.casesOn then return (miss "decide", 0)
  if c == ``Prod.mk || c == ``Prod.fst || c == ``Prod.snd || c == ``Prod.rec ||
      c == ``Prod.casesOn then
    return (repr "pairs", 0)
  if kernelNatOps.contains c then return (none, 0)
  if (`WellFounded).isPrefixOf c then return (miss "WellFounded.fix", 0)
  if (← isMatcher c) || isCasesOnRecursor env c || isRecOnRecursor env c || isSparseCasesOn c then
    return (miss "matcher", 0)
  if isAuxRecursor env c then return (miss "brecOn", 0)
  if let some info := env.getProjectionFnInfo? c then
    if info.fromClass then
      return (if isIntType args[0]? then repr "Int" else miss "instance", info.numParams + 1)
    -- a field of a structure (`Array.toList`): one step, as the primitive projection `.proj`
    return (repr "projections", info.numParams)
  if (pairExt.getState env).fst.contains c then return (miss "readable definition", 0)
  if c.components.contains `Src || inlineAttr.hasTag env c then
    return (miss "auxiliary definition", 0)
  let some (.defnInfo _) := env.find? c | return (none, 0)
  if (← isInstance c) || !isLibraryConst env roots c then return (none, 0)
  if (`Int).isPrefixOf c || ((c == ``Nat.cast || c == ``Int.cast) && isIntType args[0]?) then
    return (repr "Int", 0)
  if (`List).isPrefixOf c then return (miss "list function", 0)
  return (miss "library function", 0)

/-- The subterms read so far, and the number of subterms where each finding is. -/
abbrev AuditM := StateT (Std.HashSet Expr × Std.HashMap Finding Nat) MetaM

/-- The findings of a term, each subterm read once. Types are not read: the kernel does not
evaluate them (the binder type of a `fun`, a `∀`). -/
partial def auditTerm (roots : NameSet) (e : Expr) : AuditM Unit := do
  if (← get).fst.contains e then return
  modify fun (seen, m) ↦ (seen.insert e, m)
  let add (f : Finding) : AuditM Unit := modify fun (seen, m) ↦ (seen, m.insert f (m.getD f 0 + 1))
  match e with
  | .app .. =>
    let args := e.getAppArgs
    let mut skip := 0
    if let .const c _ := e.getAppFn then
      let (f?, n) ← classifyHead roots c args
      if let some f := f? then add f
      skip := n
    else auditTerm roots e.getAppFn
    for a in args[skip:] do auditTerm roots a
  | .const c _ =>
    if let some f := (← classifyHead roots c #[]).fst then add f
  | .lam _ _ b _ => auditTerm roots b
  | .letE _ _ v b _ =>
    add { miss := true, category := "let", what := `let }
    auditTerm roots v; auditTerm roots b
  | .mdata _ b => auditTerm roots b
  | .proj s _ b =>
    add { miss := false, category := if s == ``Prod then "pairs" else "projections", what := s }
    auditTerm roots b
  | _ => pure ()

/-- The findings of the definition `c`: what its value still contains. `roots` are the roots of
the modules of the user's code (`userRoots`). -/
def auditConst (roots : NameSet) (c : Name) : MetaM (Array (Finding × Nat)) := do
  let .defnInfo info ← getConstInfo c | throwError "kernel audit: `{c}` is not a definition"
  let (_, _, m) ← (auditTerm roots info.value).run ({}, {})
  return m.toArray.qsort fun (a, _) (b, _) ↦
    a.category < b.category || (a.category == b.category && a.what.toString < b.what.toString)

/-- `cat: c₁ ×n₁, c₂ ×n₂; cat': …`, the findings of one group. -/
def showFindings (fs : Array (Finding × Nat)) : MessageData := Id.run do
  let mut out : Array MessageData := #[]
  let mut cats : Array String := #[]
  for (f, _) in fs do
    unless cats.contains f.category do cats := cats.push f.category
  for cat in cats do
    let items := fs.filter (·.fst.category == cat) |>.map fun (f, n) ↦ m!"{f.what} ×{n}"
    out := out.push m!"{cat}: {MessageData.joinSep items.toList ", "}"
  return MessageData.joinSep out.toList "; "

end Audit

section Commands

/-- `kernel_def f …`, written as a `def`: the readable definition is `Src.f`, and `f` is its
kernel form, with the equations of `Src.f` stated on `f`. Nothing is added when the readable
definition has an error or when the equation is rejected. -/
syntax (name := kernelDefCmd)
  declModifiers "kernel_def " declId ppIndent(optDeclSig) declVal : command

@[command_elab kernelDefCmd] def elabKernelDef : CommandElab := fun stx ↦ do
  -- the attributes go to the kernel form, once it has its equations
  let attrs : Array (TSyntax ``Parser.Term.attrInstance) :=
    if stx[0][1].isNone then #[] else stx[0][1][0][1].getSepArgs.map (⟨·⟩)
  let mods : TSyntax ``Parser.Command.declModifiers := ⟨stx[0].setArg 1 mkNullNode⟩
  let id : TSyntax ``Parser.Command.declId := ⟨stx[2]⟩
  let sig : TSyntax ``Parser.Command.optDeclSig := ⟨stx[3]⟩
  let val : TSyntax ``Parser.Command.declVal := ⟨stx[4]⟩
  let name := stx[2][0].getId
  let ns ← getCurrNamespace
  let env ← getEnv
  let src := ns ++ `Src ++ name
  let dst := ns ++ name
  -- the readable definition, with its messages apart: an error among them stops here. It is
  -- elaborated in one piece (`Elab.async` off), so that an error of its compilation is seen.
  let msgs := (← get).messages
  modify fun st ↦ { st with messages := {} }
  elabCommand (← `(namespace $(mkIdent `Src)))
  try
    elabCommand (← `(set_option Elab.async false in
      $mods:declModifiers def $id:declId $sig:optDeclSig $val:declVal))
  finally
    elabCommand (← `(end $(mkIdent `Src)))
  let failed := (← get).messages.hasErrors
  modify fun st ↦ { st with messages := msgs ++ st.messages }
  -- a `private` definition: both names are private
  let env' ← getEnv
  let priv := !env'.contains src && env'.contains (mkPrivateName env' src)
  let (src, dst) := if priv then (mkPrivateName env' src, mkPrivateName env' dst) else (src, dst)
  if failed || !env'.contains src then
    setEnv env
    return
  try
    liftTermElabM do
      compile src dst
      addEquations src dst
      -- "go to definition" on the kernel form leads here
      addDeclarationRangesFromSyntax dst stx stx[2]
    unless attrs.isEmpty do
      elabCommand (← `(attribute [$attrs,*] $(mkCIdent dst)))
  catch ex =>
    setEnv env
    throwError "kernel_def `{name}` rejected: {ex.toMessageData}"

/-- `#kernel_audit`: what the kernel form of every `kernel_def` of the environment still contains,
in two groups: the misses of the compiler, which should not be there (`ite`, `dite`, a matcher,
`brecOn`, `WellFounded.fix`, `let`, `Decidable.decide`, an operation through an instance, a call
of a list function or of another function of a library, a call of a readable definition `Src.g`
or of an auxiliary one), and the representation it keeps (pairs, `Int`, the fields of a
structure, as `Array.toList`). `#kernel_audit f g` reads the definitions named (a hand-written
form, say). `#kernel_audit strict` fails if there is a miss. -/
syntax (name := kernelAuditCmd) "#kernel_audit" (&" strict")? (ppSpace ident)* : command

@[command_elab kernelAuditCmd] def elabKernelAudit : CommandElab := fun stx ↦ do
  let strict := !stx[1].isNone
  let named ← stx[2].getArgs.mapM fun id ↦ liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
  liftTermElabM do
    let env ← getEnv
    let roots := userRoots env
    let names := if named.isEmpty then
        (pairExt.getState env).snd.toArray.map (·.fst) |>.qsort (·.toString < ·.toString)
      else named
    let mut lines : Array MessageData := #[]
    let mut missLines : Array MessageData := #[]
    -- per category: the definitions where it is, and its subterms
    let mut total : Std.HashMap (Bool × String) (Nat × Nat) := {}
    let mut nMiss := 0
    let mut nRepr := 0
    for c in names do
      let fs ← auditConst roots c
      if fs.isEmpty then continue
      let misses := fs.filter (·.fst.miss)
      let reprs := fs.filter (!·.fst.miss)
      let mut cats : Array (Bool × String) := #[]
      for (f, n) in fs do
        let k := (f.miss, f.category)
        let (d, s) := total.getD k (0, 0)
        total := total.insert k (if cats.contains k then d else d + 1, s + n)
        unless cats.contains k do cats := cats.push k
      if !misses.isEmpty then
        nMiss := nMiss + 1
        missLines := missLines.push m!"\n  {.ofConstName c}: {showFindings misses}"
      else nRepr := nRepr + 1
      let parts := (if misses.isEmpty then #[] else #[m!"misses: {showFindings misses}"]) ++
        (if reprs.isEmpty then #[] else #[m!"representation: {showFindings reprs}"])
      lines := lines.push m!"\n  {.ofConstName c}: {MessageData.joinSep parts.toList " | "}"
    let summary (miss : Bool) : MessageData :=
      let ks := total.toArray.filter (·.fst.fst == miss) |>.qsort (·.fst.snd < ·.fst.snd)
      if ks.isEmpty then "none" else MessageData.joinSep (ks.toList.map fun ((_, cat), d, s) ↦
        m!"{cat} in {d} ({s} {if s == 1 then "subterm" else "subterms"})") ", "
    let head := m!"kernel audit of {names.size}: {nMiss} with a miss of the compiler, {nRepr} more \
      with a representation it keeps\nmisses: {summary true}\nrepresentation: {summary false}"
    if strict && nMiss > 0 then
      throwError m!"{head}\nthe misses:{MessageData.joinSep missLines.toList ""}"
    logInfo m!"{head}{MessageData.joinSep lines.toList ""}"

end Commands

end KernelDef
