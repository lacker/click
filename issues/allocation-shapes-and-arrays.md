# Broaden allocation forms and array declarations

Found by the 2026-09-01 kernel audit at cb034b21.

`malloc` must be directly assigned ("the fixed-size `malloc` result may not
be discarded", `src/languages/c/syntax.rs:1241-1244`); struct allocation must
literally be `malloc(sizeof(struct S))` matching the target's type
(`:1379-1400`); `sizeof` applies only to structs (`:1727-1737`), so
`n * sizeof(int)` is unwritable and runtime int32 allocation uses the magic
form `malloc(count * 4)`; broader allocation beyond the supported `calloc`
forms, `realloc`, and arbitrary byte layouts is unsupported
(`docs/concepts/resources.md:590-595`;
`docs/internals/roadmap.md:142-145`).
Local arrays take exactly one dimension suffix (`:1025-1064`), initializers
are rejected ("local array initializers are not supported", `:1145-1147`),
and struct-typed arrays are rejected (`:922-926`, `:1129-1133`).

## Violated invariant

Click should model the allocation calls and array declarations real C uses,
with the allocation authority and owned memory they produce, so that
`p = malloc(n * sizeof(int))`, `calloc`, `realloc`, and `int32 m[3][4]`
verify without rewriting.

## Intended regression

Mdtests with unchanged C: `int32* p = malloc(n * sizeof(int32));` with
`allocation(p, n * 4)`; `calloc(n, sizeof(struct S))` producing zeroed cells;
`realloc(p, m * 4)` preserving the first `min(n, m)` cells and transferring
the allocation resource; a local `int32 m[3][4]` indexed `m[i][j]` with
bounds obligations; `int32 a[3] = {1, 2, 3};`; an array of structs `struct S
items[8]` indexed by field.

## Acceptance criteria

- `sizeof` applies to every supported type and evaluates to the documented
  LP64 size; `malloc` accepts any size expression and produces an allocation
  of that symbolic byte size, with typed access obligations at use.
- `calloc` and `realloc` are modeled builtins with their lifetime
  transitions recorded in the memory DAG like `malloc` and `free`.
- Multidimensional arrays, initializers, and arrays of structs parse and
  lower to the existing block model with correct byte offsets.
- `scripts/check.sh` passes.

Related: [struct-model.md](struct-model.md);
[integer-types.md](integer-types.md) for `size_t` sizes.
