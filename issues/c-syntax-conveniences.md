# Parse the everyday C syntax the C0 frontend rejects

Found by the 2026-09-01 kernel audit at cb034b21. Each item is a parser or
lowering change whose semantics the kernel already has or can express with
existing terms; none needs new kernel state.

- **`else if` and unbraced bodies (implemented).** `if`, `else`, `while`, and
  `for` now accept one controlled statement, including nested `else if`
  chains, while still requiring declarations to be enclosed in braces. The
  parser and mdtest regression landed in `2d524a83`.
- **Ternary.** `?` and `:` are unexpected characters (`:1945-1972`). The
  kernel has `Bitvector32Term::If` for value selection.
- **Casts.** There is no `(type) expr` production (`:1592-1637`, `:1752-1756`
  treats `(` as grouping only). `(int32) c` and `(uint8) x` should map to the
  existing promotion and checked narrowing; pointer casts need a decision.
- **Integer literals.** Number tokens are decimal digit runs only
  (`:1898-1906`): `0xFF` lexes as `0` then `xFF`; suffixes `U`/`L` are
  rejected; a leading-zero literal silently parses as decimal, a divergence
  from C's octal.
- **Increment and compound assignment.** `x++` exists only as a statement;
  compound assignment supports only `++ -- += -= *= ^=` (`:729-740`,
  `:1918-1935`) and only onto plain scalars: `a[i] += 1` and `p->f++` fail
  because indexed and field targets require bare `=` (`:1098-1119`).
- **For-loop forms.** Declarations require initializers, the condition is
  mandatory (`for (;;)` fails), and the step must be one scalar update
  (`:1206-1224`, `:1266-1291`; mdtest `c_for_loop_rejects_declaration`).
  Comma-separated scalar assignment/update steps are now accepted and lowered
  in source order. The initializer and step may also be omitted; the
  condition remains required.

## Violated invariant

The frontend should accept the ordinary surface forms of the C0 subset
whenever the kernel can already express their meaning, so that source is not
rewritten for syntax alone.

## Intended regression

One mdtest per bullet, each an unchanged C function that a compiler accepts,
verifying a contract that exercises the construct: an else-if ladder
returning a classification; `return c ? a : b;`; a cast from `int32` to
`uint8` with its range obligation; `flags & 0x0F`; `a[i] += 1;` and
`p->count++;`; `for (i = 0; i < n; i++, j--)` (a comma-separated step, which the
single-scalar-update step at `:1213` rejects) and `for (;;) { ... break; }`
(the latter after [non-structured-control-flow.md](non-structured-control-flow.md)).
Negative mdtests: an octal literal `010` either evaluates to 8 or is rejected,
never silently 10; a pointer cast that the model does not support is
rejected with a diagnostic.

## Acceptance criteria

- Every bullet is parsed and lowered to existing kernel forms, with
  evaluation order and value semantics matching C (compound assignment on a
  memory lvalue evaluates the lvalue once).
- `C0_PUBLIC_FORMS` and `docs/reference/language/c0.md` list the new forms.
- The mdtests above pass; `scripts/check.sh` passes.
