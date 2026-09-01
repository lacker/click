# Support pointer-to-pointer types

Found by the 2026-09-01 kernel audit at cb034b21.

Pointer types are limited to `Int32Pointer` and `UInt8Pointer`
(`src/kernel/primitives.rs:207-216`); the C0 type grammar
(`src/languages/c/syntax.rs:950-999`) has no second level of indirection.
`int**` and `char**` out-parameters, arrays of pointers, and argument vectors
are all unrepresentable, even for otherwise scalar code. Symbolic-pointer
abstraction (`src/kernel/api.rs:456-458`) handles only the two existing
pointer types; the typed load/store builders (`api.rs:609-618`, `:702-712`)
accept any `CType`, but pointee resolution (`CType::pointee_type`,
`src/kernel/primitives/term_operations.rs:624`; `c_expression_pointee_type`,
`src/kernel/eval/expression.rs:660-681`) knows only those two.

## Violated invariant

Click should model pointers to pointers (at least `T**` for every supported
`T`) with typed loads and stores of pointer values, so that out-parameter and
pointer-array idioms verify without rewriting.

## Intended regression

Mdtests with unchanged C: `int32 get(int32** out, int32* src) { *out = src;
return 0; }` with `ensures *out == src`; iterating `char** argv` up to a
null; storing a freshly allocated block through an `int32**` out-parameter
with the allocation resource transferred to the caller's pointee.

## Acceptance criteria

- `CType` gains a general pointer constructor over pointee types (or at
  least `PointerPointer` variants), with 8-byte size and alignment under
  LP64, and loads/stores of pointer values through it.
- Memory provenance and resource ranges treat a pointer-valued cell like an
  int32 cell for framing and ownership.
- Surface Click can declare and index such parameters in contracts.
- `scripts/check.sh` passes.

Related: [struct-model.md](struct-model.md) for pointers to struct fields
that are themselves pointers.
