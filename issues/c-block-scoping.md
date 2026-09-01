# Model C block scope for local declarations

Found by the 2026-09-01 kernel audit at cb034b21. Reproduced with
`click verify` (exit 0) for both a scalar and a struct-pointer shadowing case.

In C a local declared inside an inner block is a distinct object that shadows
an outer variable of the same name and dies at block exit. The C0 parser
(`src/languages/c/syntax.rs:1125-1167`) tracks no scopes and emits `Declare`
inline with no redeclaration check; `CFunction::new`
(`src/kernel/primitives/contracts.rs:21-43`) does no body validation;
`declare_local` (`src/kernel/eval/statements.rs:1188-1218`) calls
`locals.set_uninitialized`, a plain map insert-overwrite
(`src/kernel/primitives/memory_state.rs:51-54`), and re-registers the memory
block keyed by name alone through `local_pointer -> "local:{name}"`
(`memory_state.rs:638-643`). Nothing restores the outer binding at block exit
(`Seq` just chains states). The parser's `variable_structs` map
(`syntax.rs:762`, `:928-932`, `:1135-1138`) is likewise flat, so after
`if (...) { struct T *p = ...; }` every later `p->field` resolves against
`T`'s layout (`resolve_field_access`, `syntax.rs:1694-1724`) and lowers to the
wrong byte offset. `docs/reference/language/c0.md` does not exclude
block-scoped declarations from the subset.

## Violated invariant

The trusted frontend and model must give in-subset C its C semantics. An
inner-block declaration must be a distinct object whose binding ends at block
exit, and a field access must resolve against the layout of the variable in
scope at that point.

## Intended regression

```c
int32 shadow(int32 c) { int32 y = 10; if (c < 0) { int32 y = 5; } else { int32 y = 5; } return y; }
```

Real C returns 10 for every input. Today `ensures result == 5 by auto;`
verifies and `ensures result == 10` is rejected with "left side evaluated to
5, right side evaluated to 10".

```c
struct S { int32 a; int32 b; }; struct T { int32 b; int32 z; };
int32 pick2(struct S* p, struct T* q, int32 c) { if (c < 0) { struct T *p = q; p->b = 1; } return p->b; }
```

With `requires c >= 0; requires p->a == 42; requires p->b == 7;` and view
resources on both objects, today `ensures result == 42` verifies (the value of
`p->a`). Real C returns 7.

After the fix: either both programs verify their true postconditions
(`result == 10`, `result == 7`) and reject the false ones, or the frontend
rejects the shadowing declaration with a positioned diagnostic. Rejection is
an acceptable first step only if documented as a subset restriction in
`docs/reference/language/c0.md`.

## Acceptance criteria

- Block-scoped declarations are either modeled (scope-indexed local keys or
  alpha-renaming in the parser, plus scoped `variable_structs`) or rejected
  when they shadow a parameter or an in-scope local; no path silently
  overwrites.
- If modeled, the outer binding and its memory block are restored at block
  exit on every path, including branches and loop bodies, and a kernel unit
  test pins that.
- Negative mdtests for both regressions; positive mdtests for the true
  postconditions if modeled.
- `scripts/check.sh` passes.
