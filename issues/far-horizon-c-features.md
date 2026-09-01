# Placeholder for floating point, function pointers, varargs, volatile, and concurrency

Found by the 2026-09-01 kernel audit at cb034b21. This file exists so the
gap list is complete; none of these has a near-term regression design.
Split any item into its own issue when work on it starts, and delete this
file when the last one is split.

- **Floating point.** `CValue` and `CType` have no float or double variant
  (`src/kernel/primitives.rs:200-216`), the parser has no float syntax
  (`src/languages/c/syntax.rs:111-119`, `:964`), and floats are absent even
  from the roadmap's type list (`docs/internals/roadmap.md:83-86`). The pilot
  target json-c represents numbers as `double`.
- **Function pointers.** No function-pointer type or call-through-pointer
  syntax (`syntax.rs:950-999`, `C0Type` at `:111-119`, `CType`). Callbacks,
  comparators, deleters, and dispatch tables are inexpressible; existing
  callback coverage models callbacks as proof-side resources
  (`mdtests/callback_resource_*.md`), not C function pointers.
- **Varargs, `volatile`, concurrency, atomics.** None has syntax or kernel
  semantics, and the roadmap does not mention them, so there is no documented
  rejection story for code that uses them.
- **Shadowing block-scoped declarations.** The kernel keys a local by its
  name alone (`local:{name}`), so the parser rejects a declaration that
  shadows a parameter or an enclosing local
  (`mdtests/c_block_scope_rejects_shadowing_local.md`); sibling blocks may
  reuse a name. Modeling block scope properly (scope-indexed local keys and a
  scoped struct-layout map) would lift the restriction.
- **Resource exhaustion outside the heap.** Stack depth for recursion,
  address-space limits, and allocation of locals are unmodeled, so a
  verified function can still crash the real machine. This is a documentation
  gap as much as a modeling one: `docs/concepts/what-click-proves.md` should
  state the caveat.

## Violated invariant

Every C construct Click does not model should be rejected with a diagnostic
that names it, and the documentation should state what a "verified" verdict
does and does not cover.

## Intended regression

For now: negative mdtests showing that `double x;`, a function-pointer
declaration, `...` in a parameter list, and `volatile int32 v;` each produce
a positioned "unsupported" diagnostic naming the construct, and a
documentation check that `what-click-proves.md` lists stack and
address-space exhaustion as outside the judgment.

## Acceptance criteria

- The four negative mdtests exist and pass; the documentation caveat lands.
- Each item is split into its own issue with a real regression design before
  implementation begins.
