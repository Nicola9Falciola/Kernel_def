# `kernel_def`: kernel forms compiled from readable definitions

A check decided by `decide +kernel` is a Boolean that Lean's kernel reduces to `true`. How long
that takes depends on the term the kernel is given, not only on the function it computes. The
fast terms (bare recursors, `Nat.*` heads, raw literals, `Bool.rec` on `Nat.ble`) used to be
written by hand, and were hard to read. `kernel_def` (`KernelDef/KernelForm.lean`, namespace
`KernelDef`) lets the definition be written as an ordinary `def` and produces the fast term from
it, with a proof, checked by the kernel, that the two are equal.

This document explains what the command does, what it produces, how the equation is proved, what
it accepts and rejects, and what it buys, with the compiler's own output as examples. The
examples are definitions of this repository: its tests in `KernelDefTest/`, its library forms,
its bench files. Those written out in this document are in `KernelDefTest/DocExamples.lean`, where
the build checks them: every output quoted here is pinned there by `#guard_msgs`. How the
compiler is measured is in `docs/MEASURING.md`. The compiler was first written for
ModularSymbolsTau, a certified computation of modular forms: how it was developed and measured
there is in `docs/history/`.

## Why kernel forms

The kernel evaluates a definition by unfolding it. Every layer the elaborator puts between the
source and the arithmetic is unfolded again at every use: the instance chain of `a + b`, the
`Decidable` instance of an `if`, the `brecOn` bookkeeping of structural recursion, a matcher, a
`let`, a pair and its projections. On literals, the kernel of Lean `v4.37.0-rc1` runs `Nat.add`,
`Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.pow`, `Nat.gcd`, `Nat.beq`, `Nat.ble`, `Nat.land`,
`Nat.lor`, `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight` (and `Nat.succ`) as single GMP operations,
but only when they appear as such. `Nat.blt` is one unfolding to `Nat.ble`. `Nat.log2` is not a
primitive: the kernel runs its definition, a `Nat.rec` with one step a bit of the argument (about
57 k instructions a bit; `log2 (2 ^ 1000000)` costs 830 G), so it has a kernel form
(`natLog2`, `KernelDef/NatForms.lean`) and the audit reports a call of it.

The cost of each construct against its fast form, per use inside a loop (`docs/history/E14.md`;
each measured on its own in `docs/techniques/`):

| construct | fast form | extra cost per use |
|---|---|---|
| `r + 3` (`HAdd.hAdd`) | `Nat.add r 3` | about +60 % of a loop step |
| `if r ≥ 7 then … else …` | `Bool.rec … (Nat.ble 7 r)` | 4.8 times the raw test |
| structural recursion (`brecOn`) | a bare `Nat.rec` / `List.rec` | 2.7 times per element |
| `a && b` | nested `Bool.rec` | +8.5 k instructions |
| `let x := v; …` | `v` written out | +7.8 k |
| a pair and its projection | two arguments | +12.9 k |
| the numeral `3` (`OfNat`) | `nat_lit 3` | under 1 % |

Written by hand, the fast form of even a short loop is hard to read. The sum of the `n` slots of
`K` bits of `x` that are at most `t`, by hand:

```lean
noncomputable def sumSmallHand (K t : ℕ) : ℕ → ℕ → ℕ :=
  @Nat.rec (fun _ ↦ ℕ → ℕ) (fun _ ↦ nat_lit 0)
    (fun _ ih x ↦
      @Bool.rec (fun _ ↦ ℕ) (ih (Nat.shiftRight x K))
        (Nat.add (Nat.land x (Nat.sub (Nat.shiftLeft (nat_lit 1) K) (nat_lit 1)))
          (ih (Nat.shiftRight x K)))
        (Nat.ble (Nat.land x (Nat.sub (Nat.shiftLeft (nat_lit 1) K) (nat_lit 1))) t))
```

With `kernel_def` it is written:

```lean
/-- The sum of the `n` slots of `K` bits of `x` that are at most `t`. -/
kernel_def sumSmall (K t : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, x =>
    if x &&& (1 <<< K - 1) ≤ t then (x &&& (1 <<< K - 1)) + sumSmall K t n (x >>> K)
    else sumSmall K t n (x >>> K)
```

and the compiler produces the first term from the second, up to η: it keeps every binder
(`example : @sumSmall = @sumSmallHand := rfl` holds).

## What `kernel_def f …` adds

`kernel_def` has the syntax of `def`: modifiers, attributes, a signature, a body by `:=` or by
pattern matching. For `kernel_def f …` in namespace `N` it adds:

| declaration | what it is |
|---|---|
| `N.Src.f` | the readable definition, an ordinary `def` of what is written |
| `N.f` | the kernel form, with the same type |
| `f.eq_src : ∀ xs, f xs = Src.f xs` | the equation, a term built by the compiler and checked by the kernel |
| `f.src_eq : @Src.f = @f` | the same at the level of functions: the rule with which a later `kernel_def` that calls `f` is compiled |
| `f.eq_src_fun : @f = @Src.f` | a `csimp` lemma: compiled code (`#eval`) runs the readable definition |
| `f.eq_1`, `f.eq_2`, …, `f.eq_def` | the equations of `Src.f`, stated on `f` under the names Lean reserves for the equations of `f` |

The readable definition is elaborated in the namespace `N.Src`, so a call of an earlier
`kernel_def g` of the same namespace resolves to `Src.g`, and the compiler replaces it by `g` with
`g.src_eq`. A `g` of another namespace may resolve to its kernel form directly, and is kept: so
`Src.f` is readable down to such calls, not always all the way down.

`f` is marked as a recursive definition, so `simp` rewrites with the equations and does not unfold
`f` to its recursors. An attribute written on the `kernel_def` (`@[simp]`, `@[grind =]`) goes to
`f`, and the docstring is copied to `f`.

For `sumSmall`, as Lean prints them:

```
def KernelDefTest.DocExamples.sumSmall : ℕ → ℕ → ℕ → ℕ → ℕ :=
fun K t x x_1 ↦
  Nat.rec (motive := fun _ ↦ ℕ → ℕ) (fun x ↦ nat_lit 0)
    (fun n n_ih x ↦
      Bool.rec (n_ih (x.shiftRight K))
        ((x.land ((Nat.shiftLeft (nat_lit 1) K).sub (nat_lit 1))).add (n_ih (x.shiftRight K)))
        ((x.land ((Nat.shiftLeft (nat_lit 1) K).sub (nat_lit 1))).ble t))
    x x_1

sumSmall.eq_src : ∀ (K t x x_1 : ℕ), sumSmall K t x x_1 = Src.sumSmall K t x x_1
sumSmall.eq_1 : ∀ (K t x : ℕ), sumSmall K t 0 x = 0
sumSmall.eq_2 : ∀ (K t x n : ℕ),
  sumSmall K t n.succ x =
    if x &&& 1 <<< K - 1 ≤ t then (x &&& 1 <<< K - 1) + sumSmall K t n (x >>> K) else sumSmall K t n (x >>> K)
```

So there are two views of one constant:

- the kernel, and every check decided by `decide +kernel`, sees the kernel form
  (`example : sumSmall 4 9 3 0x7a3 = 10 := by decide +kernel`: the slots 3, 10 and 7, of which
  3 and 7 are at most 9);
- a proof sees the readable definition: `rw [sumSmall]`, `simp [sumSmall]` and `unfold sumSmall`
  use `sumSmall.eq_1`, `sumSmall.eq_2`, which are about `sumSmall` itself. A lemma is proved from
  them and never mentions a recursor:

  ```lean
  theorem sumSmall_zero_right (K t n : ℕ) : sumSmall K t n 0 = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simp [sumSmall, ih]
  ```

A client names `f`, not `Src.f`. A `kernel_def` that replaces an ordinary definition keeps its name
and the order of its arguments, so the files that name it do not change.

## The compiler is not trusted

The compiler is ordinary metaprogramming, outside the trusted base: what it produces is checked.

- `f.eq_src` is added with `addDecl`, so the kernel checks its proof. A compiler bug that produces
  a wrong kernel form produces an equation the kernel rejects.
- The axioms of every generated theorem are collected; one outside `propext`,
  `Classical.choice`, `Quot.sound` rejects the definition.
- When the readable definition has an error (a type error, a call of a `noncomputable` function
  in a computable definition), or the compiler fails, or the kernel rejects the equation, the
  environment is put back as it was and `kernel_def` reports an error: nothing is added, neither
  `f` nor `Src.f`.
- What a check means is proved about `f` through its readable equations (as
  `sumSmall_zero_right` above), and those equations are theorems. So a kernel form is either equal to the
  readable definition, or it does not exist.

A wrong compiler can therefore only fail to compile, or compile to an equal term that costs more.
The second is what the term gate and the audit are for (`docs/MEASURING.md`).

## How a definition is compiled

The body is translated recursively. Each step returns the new term and, when the step is not a
definitional unfolding, a proof that the old and the new terms are equal; the proofs are chained
into `f.eq_src`.

| written | kernel form | the step's proof |
|---|---|---|
| `a + b`, `-`, `*`, `/`, `%`, `^`, `&&&`, `|||`, `^^^`, `<<<`, `>>>` on `ℕ` | `Nat.add a b`, `Nat.sub`, `Nat.mul`, `Nat.div`, `Nat.mod`, `Nat.pow`, `Nat.land`, `Nat.lor`, `Nat.xor`, `Nat.shiftLeft`, `Nat.shiftRight` | definitional |
| a numeral of `ℕ` | a raw literal (`nat_lit`) | definitional |
| `a ≤ b`, `a < b`, `a = b`, `a == b` on `ℕ`, as Booleans | `Nat.ble a b`, `Nat.blt a b`, `Nat.beq a b` | definitional |
| `a && b`, `a \|\| b`, `!a`, `bif c then t else e`, `a != b` | `Bool.rec` | definitional (each unfolds to a `Bool.rec`) |
| `if c then t else e` | `Bool.rec e t (decide c)`, with `decide c` compiled as above | `ite_eq_boolRec` |
| `∧`, `∨`, `¬`, `≠` in a condition | nested `Bool.rec` | `decide_and_eq_boolRec`, `decide_or_eq_boolRec`, `decide_not_eq_boolRec`, `decide_ne_eq_boolRec` |
| `let x := v; b` | `b` with `v` written in place of `x` | definitional |
| `match` | the recursor of the type (`Nat.rec`, `List.rec`, `Int.rec`, …) with a constant motive | definitional; a `match` with overlapping patterns (`\| _, _ => false`) by a split into cases |
| `l.all p`, `l.any p`, `l.foldr f b`, `l.map f` | a `List.rec` | `list_all_eq_rec`, `list_any_eq_rec`, `list_foldr_eq_rec`, `list_map_eq_rec` |
| `l.length`, `l.getD i d`, `l.headD d`, `l.tail`, `List.replicate n a`, `List.range' s n step`, `List.range n`, `l.eraseIdx i`, `l.filter p`, `as ++ bs`, `as.zip bs` | `listLength l`, `listGetD l i d`, `listHeadD l d`, `listTail l`, `listReplicate n a`, `listRange' s n step`, `listRange' 0 n 1`, `listEraseIdx l i`, `listFilter p l`, `listAppend as bs`, `listZip as bs`: kernel forms with bare recursors (`KernelDef/ListForms.lean`), in every module that imports it | `length_eq_listLength`, `getD_eq_listGetD`, …, rules marked `@[kernel_rule]` |
| `l.length`, where `KernelDef/ListForms.lean` is not imported | a `List.rec` written in place, one `Nat.add` a cons | `list_length_eq_rec`, a built-in rule |
| `l.foldl f b`, `l.sum` (`ℕ`; any `[Add α] [Zero α]`), `l.reverse`, `l.take n`, `l.drop n`, `List.zipWith f l r`, `l.flatten`, `l.flatMap f`, `l[i]?`, `l[i]?.getD d`, `l[i]!`, `l.find? p`, `l.elem a`, `l.contains a`, `decide (a ∈ l)` (`ℕ`; any `[BEq α]`), `l.count a`, `l.lookup a` (`ℕ`), `l.max?` (`ℕ`), `decide (l = r)` and `l == r` (`List ℕ`) | `listFoldl`, `listSumNat` / `listSum`, `listReverseAux l []`, `listTake`, `listDrop`, `listZipWith`, `listFlatten`, `listFlatMap`, `listGet?`, `listGetD`, `listGetD l i 0` (`default : ℕ` is `0`), `listFind?`, `listElemNat` / `listElem`, `listCountNat`, `listLookupNat`, `listMaxNat?`, `listBEqNat` (`KernelDef/ListForms.lean`) | rules marked `@[kernel_rule]` |
| `a.foldl f b`, `a[i]!`, `a.size` on `Array` | `listFoldl f b a.toList`, `listGetD a.toList i default`, `listLength a.toList` | rules (`KernelDef/ListForms.lean`) |
| `o.getD d` on `Option` | `Option.rec d (fun a ↦ a) o` | `option_getD_eq_rec` |
| `n.choose k` | `natChoose n k`, a kernel form with a bare `Nat.rec` (`KernelDef/ListForms.lean`) | `choose_eq_natChoose`, a rule marked `@[kernel_rule]` |
| `n.log2`, `n.sqrt`, `m.testBit j`, `min a b`, `max a b`, `n.pred`, `Nat.lcm m n`, `Nat.all n fun i _ ↦ f i`, `decide (∀ i < n, p i)` on `ℕ` | `natLog2`, `natSqrt`, `natTestBit`, `Bool.rec` on `Nat.ble` (twice), `n - 1`, `m * n / Nat.gcd m n`, `natAll` (`KernelDef/NatForms.lean`) | rules |
| `a + b`, `a - b`, `a * b`, `-a`, `a / b`, `a % b`, `a.natAbs`, `a.toNat`, `decide (a < b)`, `decide (a ≤ b)`, `decide (a = b)` on `ℤ` | the kernel forms of the core: `Int.add_k`, `Int.sub_k`, `Int.mul_k`, `Int.neg_k`, `Int.ediv_k`, `Int.emod_k`, `Int.natAbs_k`, `Int.toNat_k`, `Int.blt'`, and `intBEq` (`KernelDef/IntForms.lean`) | rules |
| `decide (Nat.Prime p)`, `Nat.fib n`, `Nat.factorial n`, `Nat.digits b n`, where the optional `KernelDef/MathlibForms.lean` is imported | `natPrime` (trial division to `√p`), `natFibAux n 0 1`, `natFactorial`, `natDigits` | rules |
| structural recursion on an argument | the recursor on that argument; the arguments that change in a recursive call are carried through the motive (`fun _ ↦ ℕ → ℕ` above); a call on a constructor rebuilt from the fields of a case (`y :: rows` after matching `x :: y :: rows`) is the call on the field it rebuilds | by induction (below) |
| a call of a `@[kernel_inline]` definition | its body, written out | definitional |
| a call of the readable form of an earlier `kernel_def` | its kernel form | its `g.src_eq` |
| an equation marked `@[kernel_rule]` | its right-hand side | the equation |
| anything else: pairs, projections, calls of plain `def`s, `Int` arithmetic | kept, its arguments compiled | — |

Rules are found by the head constant of the term, and the first that applies is used. The
`@[kernel_rule]`s of the environment are tried first, then the built-in rules of the compiler
(`builtinRules`, appended after them by `mkContext`): so `l.length` becomes `listLength l` where
`KernelDef/ListForms.lean` is imported, and a `List.rec` written in place
(`list_length_eq_rec`) where it is not. Either way the kernel walks the list with a bare
recursor.

The compiler then shares equal subterms (`ShareCommon`), as Lean does for every definition.

### The three kinds of equation

The compiler records, for every definition, how its equation was proved:

- by unfolding: every step was definitional, and `f.eq_src` is the unfold equation of `Src.f`
  read at the type `f xs = Src.f xs` (`mask` and `scale`, under Examples);
- by rewriting: some step used a lemma of the table (`ite_eq_boolRec`, `list_all_eq_rec`, an
  earlier `g.src_eq`), and the proof chains them (`splitsOk` below, `field`, which calls `mask`);
- by induction: the definition recurses. The proof is the recursor of the same type with the
  motive `fun y ↦ ∀ vs, Src.f … y … vs = f … y … vs`; in each case it takes the unfold equation
  of `Src.f` at the constructor, translates the body with the induction hypothesis standing for
  the recursive calls, and closes the case (`sumSmall`, `sumL`, `allZip`, `sumTo`). This is where
  the compiler goes beyond the `dag%` compiler of the Lean Kernel Challenge submission it was
  modelled on: the checks recurse over lists and depths that are variables, not over literals, so
  the equation has to hold for every argument, not be computed for one.

### `@[kernel_inline]`: a helper with a name in the source only

A helper worth naming in the source but not worth a function call in the kernel is marked
`@[kernel_inline]`; the compiler writes its body where it is called:

```lean
@[kernel_inline] def low (K x : ℕ) : ℕ := x % K
@[kernel_inline] def high (K x : ℕ) : ℕ := x / K

kernel_def splitsOk (K b : ℕ) (A : List ℕ) : Bool :=
  A.all fun x ↦ low K x < high K x && high K x < b
```

The kernel form has neither `low` nor `high`:

```
def KernelDefTest.DocExamples.splitsOk : ℕ → ℕ → List ℕ → Bool :=
fun K b A ↦
  List.rec true (fun a x ih ↦ Bool.rec false ih (Bool.rec false ((a.div K).blt b) ((a.mod K).blt (a.div K)))) A
```

`List.all` became a `List.rec`, `&&` a `Bool.rec` (the second test is not evaluated when the first
fails), `<` `Nat.blt`, and `%` and `/` `Nat.mod` and `Nat.div`.

## Examples

All the output below is Lean's (`#print`, `#check`, with `set_option pp.natLit true`), as
`KernelDefTest/DocExamples.lean` pins it; `allZip` and `sumTo` are definitions of
`KernelDefTest/Shapes.lean`, printed there too.

### A definition without recursion

```lean
kernel_def mask (k : ℕ) : ℕ := 1 <<< k - 1
kernel_def field (W i x : ℕ) : ℕ := (x >>> (W * i)) &&& mask W
```
```
def KernelDefTest.DocExamples.field : ℕ → ℕ → ℕ → ℕ :=
fun W i x ↦ (x.shiftRight (W.mul i)).land (mask W)
field.eq_src : ∀ (W i x : ℕ), field W i x = Src.field W i x
field.eq_1 : ∀ (W i x : ℕ), field W i x = x >>> (W * i) &&& mask W
```

The notations became `Nat.shiftRight`, `Nat.mul` and `Nat.land`. `mask` is itself a `kernel_def`
and stays a call: the readable `field` calls `Src.mask`, which the compiler replaced by `mask` with
`mask.src_eq`, so the equation of `field` is by rewriting, and that of `mask` by unfolding.

### Recursion on a list

```lean
kernel_def sumL : List ℕ → ℕ
  | [] => 0
  | x :: t => x + sumL t
```
```
def KernelDefTest.DocExamples.sumL : List ℕ → ℕ :=
fun x ↦ List.rec (nat_lit 0) (fun head tail tail_ih ↦ head.add tail_ih) x
sumL.eq_1 : sumL [] = 0
sumL.eq_2 : ∀ (x_1 : ℕ) (t : List ℕ), sumL (x_1 :: t) = x_1 + sumL t
```

One `Nat.add` per element, no `brecOn` and no `HAdd` instance (`docs/techniques/length/` measures
the same difference on the length of a list). The equation is by induction.

### Two lists walked together

`allZip`, of `KernelDefTest/Shapes.lean`:

```lean
kernel_def allZip {α β : Type*} (f : α → β → Bool) : List α → List β → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && allZip f as bs
  | _, _ => false
```
```
def KernelDefTest.Shapes.allZip.{u_1, u_2} : {α : Type u_1} →
  {β : Type u_2} → (α → β → Bool) → List α → List β → Bool :=
fun {α} {β} f x x_1 ↦
  List.rec (motive := fun _ ↦ List β → Bool) (fun x ↦ List.rec true (fun head tail tail_ih ↦ false) x)
    (fun head tail tail_ih x ↦
      List.rec false (fun head_1 tail tail_ih_1 ↦ Bool.rec false (tail_ih tail) (f head head_1)) x)
    x x_1
```

The recursion is on the first list; the second is carried through the motive
(`fun _ ↦ List β → Bool`) and matched by a `List.rec` in each case. The last pattern overlaps
the other two, so Lean states its equation with hypotheses, and so does `allZip.eq_3`:

```
@Shapes.allZip.eq_3 : ∀ {α : Type u_1} {β : Type u_2} (f : α → β → Bool) (x : List α) (x_1 : List β),
  (x = [] → x_1 = [] → False) →
    (∀ (a : α) (as : List α) (b : β) (bs : List β), x = a :: as → x_1 = b :: bs → False) → Shapes.allZip f x x_1 = false
```

### A match on an integer, and a carried argument

```lean
kernel_def scale (c : ℤ) (x : ℕ × ℕ) : ℕ × ℕ :=
  match c with
  | Int.ofNat k => (k * x.fst, k * x.snd)
  | Int.negSucc k => ((k + 1) * x.snd, (k + 1) * x.fst)

kernel_def sumTo : ℕ → ℕ → ℕ
  | acc, 0 => acc
  | acc, n + 1 => sumTo (acc + n) n
```
```
def KernelDefTest.DocExamples.scale : ℤ → ℕ × ℕ → ℕ × ℕ :=
fun c x ↦
  Int.rec (fun a ↦ (a.mul x.fst, a.mul x.snd)) (fun a ↦ ((a.add (nat_lit 1)).mul x.snd, (a.add (nat_lit 1)).mul x.fst))
    c

def KernelDefTest.Shapes.sumTo : ℕ → ℕ → ℕ :=
fun x x_1 ↦ Nat.rec (motive := fun _ ↦ ℕ → ℕ) (fun x ↦ x) (fun n n_ih x ↦ n_ih (x.add n)) x_1 x
```

The matcher of `scale` became `Int.rec`. Its pairs stay: the compiler does not change
representation, and a client marks such a definition with `-- TODO: kernel form: …`.
`#kernel_audit scale` lists them:

```
kernel audit of 1: 0 with a miss of the compiler, 1 more with a representation it keeps
misses: none
representation: pairs in 1 (4 subterms)
  scale: representation: pairs: Prod.fst ×1, Prod.mk ×2, Prod.snd ×1
```

`sumTo` recurses on its second argument and changes the first in the recursive call: the first is
carried through the motive (`fun _ ↦ ℕ → ℕ`), and the recursor is applied to the second, then to
the first (`… x_1 x`). Where the equation compiler uses `Nat.brecOn`, the kernel form has a bare
`Nat.rec`. `KernelDefTest/Shapes.lean` also has `powAcc`, whose argument after the one recursed
on does not change and is not carried.

### A library form: `List.length`

`List.length` is defined by structural recursion with `HAdd`, so the kernel would unfold `brecOn`
and the instance chain at every element (`docs/techniques/length/`: 3.7 times the cost of a bare
recursor). `KernelDef/ListForms.lean` gives it a kernel form, and a rule:

```lean
kernel_def listLength : List α → ℕ
  | [] => 0
  | _ :: t => listLength t + 1

@[kernel_rule]
theorem length_eq_listLength : @List.length α = listLength := by
  funext l
  induction l with
  | nil => rfl
  | cons a l ih => simp [listLength, ih]
```
```
def KernelDef.listLength.{u_1} : {α : Type u_1} → List α → ℕ :=
fun {α} x => List.rec (nat_lit 0) (fun head tail tail_ih => tail_ih.add (nat_lit 1)) x
```

The rule is an equation between functions, so it applies to `List.length` at any type and with
any argument. A readable definition keeps `l.length`, and its kernel form calls `listLength`
(`KernelDefTest/LibraryForms.lean`, which pins the term with `#guard_msgs`):

```lean
kernel_def lenPlus (l : List ℕ) (n : ℕ) : ℕ := l.length + n
```
```
def KernelDefTest.LibraryForms.lenPlus : List ℕ → ℕ → ℕ :=
fun l n ↦ (KernelDef.listLength l).add n
```

`#kernel_audit strict lenPlus` finds no miss. `bench/Length.lean` and `bench/LengthSrc.lean`
decide `len l = m` for lists of `2^10` to `2^14` elements through `listLength` and through core's
`List.length`: 1.04 against 3.79 G of kernel instructions, and 1199 against 4390 heartbeats for the
`2^14` check (`docs/MEASURING.md`, "Baseline").

The other library forms work the same way. `List.getD` is defined through `Option` and
`GetElem`, `List.replicate`, `List.eraseIdx` and `List.filter` through `brecOn`; each has a
kernel form and a rule.

In a module that imports `KernelDef.ListForms` (a client imports `KernelDef`, which imports it),
a readable definition keeps calling the functions of the core (`KernelDefTest/LibraryForms.lean`):

```lean
kernel_def sumFirst (l : List ℕ) (k : ℕ) : ℕ :=
  ((List.range k).map fun i ↦ l.getD i 0).foldr (· + ·) 0
```
```
def KernelDefTest.LibraryForms.sumFirst : List ℕ → ℕ → ℕ :=
fun l k ↦
  List.rec 0 (fun a x ih ↦ a.add ih)
    (List.rec [] (fun a x ih ↦ KernelDef.listGetD l a 0 :: ih) (KernelDef.listRange' 0 k 1))
```

`List.range k` became `listRange' 0 k 1` and `l.getD i 0` `listGetD l i 0`, by the rules of
`KernelDef/ListForms.lean`; `List.map` and `List.foldr` became `List.rec`s written in place, by
the built-in rules.

The same holds for `l.headD d`, `l.tail`, `List.replicate n a`, `List.range' s n step`,
`l.eraseIdx i`, `l.filter p`, `as ++ bs` and `as.zip bs` (`listHeadD`, `listTail`, `listReplicate`,
`listRange'`, `listEraseIdx`, `listFilter`, `listAppend`, `listZip`); `List.range n` is written
`listRange' 0 n 1`.

### The library forms

The library has 42 kernel forms and 64 rules beyond the built-in ones, in four modules: the
functions of the core on lists, arrays and `Option`, and `Nat.choose` (`KernelDef/ListForms.lean`),
those on `ℕ` (`KernelDef/NatForms.lean`), those on `ℤ` (`KernelDef/IntForms.lean`, the kernel
forms the core itself ships in `Init/Data/Int/Kernel.lean`), and, in a module the root does not
import, Mathlib's `decide (Nat.Prime p)`, `Nat.fib`, `Nat.factorial`, `Nat.digits`
(`KernelDef/MathlibForms.lean`). The table above lists them. Which functions were chosen, and what
each buys, is in `docs/library_forms/README.md`. Five of them do more than save a constant factor:
on `Nat.log2`, `List.max?`, `Array.foldl`, `Nat.all` and `decide (∀ i < n, p i)` the kernel is
superlinear (`List.max?` costs 1339 G at `2^14` elements, its kernel form 1.1 G), and on
`Array.foldl`, `Nat.all`, `decide (∀ i < n, p i)` and `decide (Nat.Prime p)` it runs out of
memory at a few thousand elements.

What a rule must respect:

- Its left side is matched with reducible transparency, instances included. A rule at `ℕ`
  names the instances Lean synthesizes there: `List.elem` at `ℕ` has
  `instBEqOfDecidableEq instDecidableEqNat`, `List.sum` has `instAddNat` and Mathlib's
  `MulZeroClass.toZero`. A source that elaborates other instance terms is not matched, and the
  audit reports the call.
- The rules of a head are tried in the order they were declared, imported ones first: the rule
  at `ℕ` (`elem_eq_listElemNat`) before the generic one (`elem_eq_listElem`), the specific
  `l[i]?.getD d` before the general `o.getD d`, and a rule before the `kernel_def`s whose sources
  call its function (`log2_eq_natLog2` before `natSqrt`, so that the kernel form of `natSqrt`
  calls `natLog2`).
- Its right side is translated again, so it may be written in notation (`min a b = if a ≤ b then
  a else b`), and it must not call its own left side: it would be rewritten by itself. `natLog2`
  bounds its search by a fuel rather than falling back to `Nat.log2`, and `natDigits` writes the
  bases `0` and `1` out.
- A rule whose left side has a numeral pattern unifies it with literals: a first rule
  `Nat.digits (b + 2) n = …` matched `Nat.digits 10 n` with `b := 8` and left `Nat.add 8 2` in
  the kernel form; `digits_eq_natDigits` is stated for every base.
- A generic form keeps the instance of its class (`listElem [BEq α]`, `listSum [Add α] [Zero α]`):
  it saves the `brecOn`, not the instance chain, and the audit reports its instance. The form at
  `ℕ` is the fast one.

### A call on a rebuilt constructor

A definition may match two cells, `x :: y :: rows`, and call itself on `y :: rows`, the tail it
matched, rebuilt. The compiler takes the call as the call on the field it rebuilds: the recursion
is on the list, in the case `head :: tail` the match splits `tail` again into `head_1 :: tail'`,
and the call on `head_1 :: tail'` is `tail_ih`, the value at `tail`. In the proof, the split on
`tail` carries the induction hypothesis on `tail` into each case, where it is about
`head_1 :: tail'`. A constructor written otherwise is found too: `n + 1` after matching `n + 2` is
`Nat.succ n`. `steps`, `pairSum` and `tri` in `KernelDefTest/Accepts.lean` are its tests.

The recursive fields of a constructor are read off the recursor (its minor premises), not off the
types of the fields, so a walk over a list of rows, a row an `abbrev` of a list, is written by
pattern matching (`entries` in `KernelDefTest/Accepts.lean`, on `List Row` with
`Row := List (ℕ × ℤ)`).

### What is rejected

```lean
kernel_def halve (n : ℕ) : ℕ := if n < 2 then 0 else 1 + halve (n / 2)

kernel_def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
```
```
error: kernel_def `halve` rejected: kernel form: `KernelDefTest.Rejects.Src.halve` is not defined by structural recursion
error: kernel_def `fib` rejected: kernel form: the recursive call
  Src.fib n
is not on a field of the constructor matched
```

Nothing is added in either case (`KernelDefTest/Rejects.lean`). `halve` recurses on `n / 2`
(well-founded recursion); `fib` calls itself on `n`, two constructors down. Its other call,
`fib (n + 1)`, is accepted: `n + 1` is the constructor `Nat.succ n` rebuilt from the case
`n + 2`, the field matched one constructor down (`tri` in `KernelDefTest/Accepts.lean`,
`| n + 2 => n + 2 + tri (n + 1)`, is accepted). Both would have to be rewritten with a fuel or
with the recursion on one constructor: a walk that recursed three cells down, for instance, reads
the list one cell at a time and carries the cells read so far.

## What the compiler does not do

- It does not change representation. Pairs, projections and `Int` stay: a definition on pairs or
  on `Int` keeps a comment `-- TODO: kernel form: …` naming what is left, and `#kernel_audit`
  lists them as representation. Constants passed as literal arguments, walking a list instead of
  indexing it and halving reads stay the author's choices (`docs/techniques/index/`,
  `docs/techniques/slotread/`).
- It rejects well-founded, mutual and nested recursion, and a recursive call that is neither on a
  field of the constructor matched nor on a constructor rebuilt from the fields of a case on such a
  field (a call three cells down, say).
- It keeps what it does not know, uncompiled: an `if h : c then …` whose proof `h` is used in the
  body stays a `dite`, a `where` helper is a second definition, to be given its own `kernel_def`,
  and a library function with no kernel form in the modules of `KernelDef/` stays a call.
  `#kernel_audit` reports each of them as a miss.
- A `match` on a numeral other than `0` followed by a wildcard (`| 0 => … | 1 => … | _ => …`) is
  compiled by Lean with `if h : n = 1`, and its kernel form keeps a `dite` and an `Eq.ndrec_symm`.
  Write the last case `| _ + 2 => …`.
- It never η-reduces: a hand-written form with fewer binders than arguments (`fun a b ↦ Nat.rec …`
  for a function of five arguments) is compiled with all of them (`fun a b x y z ↦ Nat.rec … x y z`).
  The kernel's work is the same.
- It leans on internals of the toolchain: the shape of `ite` and of `Decidable`, matchers that
  unfold to `casesOn`, the names Lean reserves for equations, `markAsRecursive`, `csimp`. After a
  bump of Lean, run the gates (`CLAUDE.md`).

## What it buys

On the checks of `bench/`, kernel instructions in G, the minimum of three runs, through the
kernel form and through the readable definition `Src.f` (`docs/MEASURING.md`, "Baseline"; the
rows in `docs/baseline/`):

| check | kernel form | `Src.f` | ratio |
|---|---:|---:|---:|
| `Shape`, a walk of packed sparse rows | 1.151 | 3.506 | 3.0 |
| `HalvingRead`, every slot of a packed natural read by halving | 2.577 | 8.765 | 3.4 |
| `RowProduct`, a product of packed rows checked row by row | 1.917 | 3.844 | 2.0 |
| `Length`, `l.length` on lists of up to `2^14` elements | 1.040 | 3.794 | 3.6 |

The two files of a pair hold the same data and the same `kernel_def`s, so the difference is that
of the checks: the kernel forms cost two to three and a half times less.

The library forms have their pairs too, each a source that calls a function of the library,
through its kernel form and through the library's function (`docs/library_forms/README.md`,
tag `libforms`): where the library is superlinear, `Log2` costs 0.011 against 4.08 G (364 times),
`ArrayFoldl` 0.048 against 12.3 G, `Prime` 0.013 against 3.49 G, `Sqrt` 0.013 against 1.79 G,
`ForallLt` 0.11 against 3.45 G, `ListMax` 0.18 against 4.91 G; where it is linear, `Count`,
`Sum`, `Reverse`, `IntLt`, `IntAdd`, `TestBit` and `Fib` cost 2.1 to 5 times less. How the compiler was
developed and measured before this repository is in `docs/history/`.

## Working with it

Writing a new one:

1. Write the definition as a `def`, in notation, with pattern matching where it recurses, and
   replace `def` by `kernel_def`. A helper that should not be a call in the kernel is a
   `@[kernel_inline] def`.
2. Look at the result: `#print f` (the kernel form), `#kernel_audit f` (what it still contains,
   below), `#check @f.eq_src`, `#print axioms f.eq_src`. A miss the audit reports (an `ite`, a
   matcher, `HAdd.hAdd`, `brecOn`, a list function of the core) means the compiler did not
   recognise that part: rewrite it, or teach the compiler (a translation, or a `@[kernel_rule]`).
3. Prove its lemmas with `rw [f]` or `simp [f]`, as for any definition.
4. When it replaces a definition a client already names, keep its name and the order of its
   arguments, and compare: the term against the old one (the term gate), or, when the term is
   meant to change, a proof that the new definition equals the old one, and the cost of the
   checks before and after (`docs/MEASURING.md`).

Adding a library form, for a function of the core or of Mathlib that readable definitions call:

1. In the module of its type (`KernelDef/ListForms.lean`, `NatForms.lean`, `IntForms.lean`; or
   the optional `MathlibForms.lean` for a function that needs more of Mathlib than the root
   imports), its kernel form as a `kernel_def` with bare recursion (`listLength` above), under the
   name of the function with the prefix of its type.
2. The equation `@[kernel_rule] theorem foo_eq_listFoo : @List.foo α = listFoo`, an equation of
   functions where it can be, proved from the readable equations (`funext`, induction, `simp`),
   with the cautions of "The library forms" above (instances, order, the right side).
3. A test in `KernelDefTest/LibraryForms.lean` (or `NatForms.lean`, `IntForms.lean`,
   `MathlibForms.lean`): a `kernel_def` whose source calls the function,
   its `#print` under `#guard_msgs` (the call is the kernel form), `#kernel_audit strict` on it,
   and an `example` decided by `decide +kernel`.
4. A bench pair, through the kernel form and through the function of the library: a generator in
   `scripts/gen_bench.py`, then `python3 scripts/gen_bench.py` (`docs/MEASURING.md`).
5. The gates (`CLAUDE.md`). The term gate reports the new form as `NEW`, and any test definition
   that calls the function as `DIFFERENT`, as intended; the audit no longer finds the call.

### The audit

`#kernel_audit f g …` prints what the kernel forms of the definitions named still contain, in two
groups. The misses of the compiler should not be there: `ite`, `dite`, a matcher (`casesOn`
included), `brecOn`, `WellFounded.fix`, `let`, `Decidable.decide`, an operation through an
instance (`HAdd.hAdd`, `LE.le`, `OfNat.ofNat`, `Max.max`, … at a type other than `ℤ`), a call of a
list function of the core or of another function of a library (`Nat.log2` included: it is no
primitive), a call of a readable definition `Src.g` or of an auxiliary one (a `where` helper, a
`@[kernel_inline]` definition left as a call). The representation is what the compiler keeps by
design: pairs (`Prod.mk`, `Prod.fst`, `Prod.snd`), `Int` (its functions, and the operations
through an instance at `ℤ`), and the fields of a structure, the primitive projection `.proj` and
the projection functions of a structure that is not a class (`Array.toList`), one step each for
the kernel. Types are not read: the kernel does not evaluate them.

Library code is told from the user's code by the root of its module. The user's roots are those
of the modules that hold a kernel form, and that of the present module (`userRoots`); a call of a
definition of any other root (the core, Mathlib) is a library call, a miss. A call of a plain
`def` of the user's code is not: it is the author's choice, as a call of another kernel form is,
and the audit reads a kernel form, not the definitions it calls. Here the roots are `KernelDef`
and `KernelDefTest`, with that of the file being checked; no root is written into the compiler. With the definitions of
`KernelDefTest/Audit.lean`:

```lean
kernel_def getOr (l : List ℕ) (i : ℕ) : ℕ := if h : i < l.length then l[i] else 0
kernel_def maxOf (a b : Bool) : Bool := max a b
kernel_def viaWhere (n : ℕ) : ℕ := go n
where go (k : ℕ) : ℕ := k + 1
kernel_def pairInt (a : ℤ) (b : ℕ) : ℤ × ℕ := (a + b, b)

#kernel_audit getOr maxOf viaWhere pairInt
```
```
kernel audit of 4: 3 with a miss of the compiler, 1 more with a representation it keeps
misses: auxiliary definition in 1 (1 subterm), dite in 1 (1 subterm), instance in 2 (2 subterms)
representation: Int in 1 (2 subterms), pairs in 1 (1 subterm)
  getOr: misses: dite: dite ×1; instance: GetElem.getElem ×1
  maxOf: misses: instance: Max.max ×1
  viaWhere: misses: auxiliary definition: KernelDefTest.AuditFaults.Src.viaWhere.go ×1
  pairInt: representation: Int: Int.add_k ×1, Nat.cast ×1; pairs: Prod.mk ×1
```

(`max` at `Bool` has no rule, the rule of `KernelDef/NatForms.lean` being at `ℕ`; the `+` of `ℤ`
is `Int.add_k`, by the rule of `KernelDef/IntForms.lean`.)

`#kernel_audit` with no name reads every `kernel_def` of the environment; `#kernel_audit strict`
is an error when there is a miss, with the list of the misses. No file of `KernelDef` runs the
command. `KernelDefTest/Audit.lean` imports every other test module and runs `#kernel_audit` over
every kernel form of the environment, the library forms of `KernelDef/` included. Not `strict`:
two tests make misses on purpose, the `dite` and `GetElem.getElem` of
`KernelDefTest.Rejects.getOr` (a proof used in the code) and the call of `Src.total.go` in
`KernelDefTest.Syn.total` (a `where` helper), and the two library forms generic in a type class
keep its instance (`BEq.beq` in `listElem`, `HAdd.hAdd` and the `0` in `listSum`). The line of
misses of the report is pinned by `#guard_msgs (substring := true)`:

```
misses: auxiliary definition in 1 (1 subterm), dite in 1 (1 subterm), instance in 3 (4 subterms)
```

so any other miss changes the line and fails `lake build`; the rest of the report is not checked.

### Checking the tree

- `lake build`: the compiler, the library forms and the tests (every `f.eq_src` checked by the
  kernel), the audit and the axiom check included.
- `python3 scripts/term_gate.py list`: every `kernel_def` of `KernelDef/` and `KernelDefTest/`.
- `python3 scripts/term_gate.py compare test/golden`: the present terms against the baseline;
  `snapshot DIR` takes a snapshot of the present terms.
- `python3 scripts/kernel_cost.py`, `python3 scripts/heartbeats.py`: the cost of a file, and of
  each declaration (`docs/MEASURING.md`).
- `scripts/run_tests.sh`: the five gates of the suite (`CLAUDE.md`, "Building").

## Where things are

- `KernelDef/KernelForm.lean`: the compiler (sections `Rules`, the rewriting lemmas; `Registry`,
  the attributes and rules; `Translation`; `Compiler`, the equation and the generated
  declarations; `Audit`, what a kernel form still contains; `Commands`, `kernel_def` and
  `#kernel_audit`).
- `KernelDef/ListForms.lean`: the kernel forms of the functions of the core on lists, arrays and
  `Option`, and of `Nat.choose`, and their `@[kernel_rule]`s; `KernelDef/NatForms.lean` and
  `KernelDef/IntForms.lean`: those on `ℕ` and `ℤ`; `KernelDef/MathlibForms.lean` (optional, not
  imported by the root): those of Mathlib's number theory.
- `KernelDefTest/`: the tests (`Accepts`, `Rejects`, `Faults`, `Shapes`, `Syntax`,
  `LibraryForms`, `NatForms`, `IntForms`, `MathlibForms`, `DocExamples`, `Audit`, `Axioms`);
  `DocExamples` holds the examples of this document.
- `bench/`: checks decided through a kernel form and through its readable definition, each file
  self-contained (it imports `KernelDef` and defines the `kernel_def`s of its check), generated by
  `scripts/gen_bench.py`.
- `KernelDef.lean`: the root, which a client imports (the compiler and the library forms but
  `MathlibForms`).
- `docs/library_forms/`: which library functions have kernel forms, and what each buys;
  `scripts/library_forms/`: its benchmark.
- `docs/MEASURING.md`: what is measured and how, and the baseline of the port (`docs/baseline/`);
  `docs/techniques/`: what each construct costs, measured alone; `docs/history/`: how the
  compiler was developed, and E14.
