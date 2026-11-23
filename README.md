# Kernel_def

Author: Nicola Falciola

`kernel_def` is a Lean 4 command that compiles a definition written in ordinary notation into a
term the kernel evaluates faster: bare recursors, the kernel's native `Nat` operations, raw
literals. The compiler is not trusted: for every definition it also adds the equation between the
two forms, `f.eq_src`, which the kernel checks.

For example, we can redefine the function that computes the length of a list as:

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

`#print listLength` shows the term the kernel evaluates:

```
def KernelDef.listLength.{u_1} : {α : Type u_1} → List α → ℕ :=
fun {α} x => List.rec (nat_lit 0) (fun head tail tail_ih => tail_ih.add (nat_lit 1)) x
```

The `@[kernel_rule]` makes the compiler use `listLength` wherever a definition calls
`List.length`. The same check through the native `List.length` costs the kernel about 3.6 times
more (`bench/Length.lean`, `docs/MEASURING.md`). More examples are in `KernelDefTest/`.

## Using the repository

- `lake exe cache get`, then `lake build`: the compiler and its whole test suite.
  `scripts/run_tests.sh` runs the build and the other gates, among them the term gate against
  `test/golden/`.
- `KernelDef/`: the compiler (`KernelForm.lean`) and the kernel forms of library functions with
  their rules (`ListForms`, `NatForms`, `IntForms`; `MathlibForms` is optional and not imported by
  `KernelDef.lean`).
- `KernelDefTest/`: what the compiler accepts, rejects and reports.
- `bench/`: each check decided through its kernel form and through its readable source, written by
  `scripts/gen_bench.py` and measured with `scripts/kernel_cost.py` and `scripts/heartbeats.py`.
- `docs/`: how the compiler works (`KERNEL_DEF.md`), how it is measured (`MEASURING.md`), which
  library functions deserve a kernel form (`library_forms/`), and how it was developed
  (`history/`).
- `CLAUDE.md`: the rules for working in the repository.

## License

Apache 2.0, see `LICENSE`.
