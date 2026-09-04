# Broaden allocation forms and array declarations

Found by the 2026-09-01 kernel audit at cb034b21.

`malloc` must be directly assigned ("the fixed-size `malloc` result may not
be discarded", `src/languages/c/syntax.rs:1241-1244`); struct allocation must
literally be `malloc(sizeof(struct S))` matching the target's type
(`:1379-1400`); `sizeof` applies only to structs (`:1727-1737`), so
`n * sizeof(int)` is unwritable and runtime int32 allocation uses the magic
form `malloc(count * 4)`; byte-oriented `uint8*` allocation was also missing,
while arbitrary byte-layout `realloc` remains unsupported
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
the allocation resource; a zeroed `calloc` prefix surviving a grown
`realloc` while its new tail remains uninitialized; a local `int32 m[3][4]`
indexed `m[i][j]` with
bounds obligations; `int32 a[3] = {1, 2, 3};`; an array of structs `struct S
items[8]` indexed by field.
Byte-buffer regressions also cover `uint8* p = malloc(n * sizeof(uint8))`
with one-byte access and `calloc(n, sizeof(uint8))` zeroing before `free(p)`.

The bounded `realloc` implementation now applies to `uint8*` and pointer
arrays as well as `int32*`, including symbolic byte extents and preserved
zeroed prefixes. Heap `malloc` and `free` now also support
`int32**`/`uint8**` pointer arrays with their eight-byte pointer stride;
pointer-array `calloc` initializes each pointer cell to null, and bounded
pointer-array `realloc` preserves fitting initialized cells and zeroed
prefixes. Heap struct pointers now use byte-backed allocation extents, accept
`malloc(count * sizeof(struct S))`, and lower `items[i].field` with the ABI
struct stride; their bounded `calloc` and `realloc` paths preserve the same
initialization and prefix rules. Arbitrary-layout `malloc` and `realloc` now
accept positive byte extents independently of the receiving pointer's logical
element width; ownership falls back to byte ranges when a typed extent is not
exactly divisible, and only complete initialized cells are copied. Compatible
external allocator declarations remain follow-up work.

## Acceptance criteria

- `sizeof` applies to every supported type and evaluates to the documented
  LP64 size; `malloc` accepts any size expression and produces an allocation
  of that symbolic byte size, with typed access obligations at use.
- `calloc` and the supported bounded `realloc` form are modeled builtins with
  their lifetime transitions recorded in the memory DAG like `malloc` and
  `free`; bounded zeroed prefixes preserve their initialization status while
  grown tails remain uninitialized. Arbitrary-byte `realloc` uses the same
  lifetime transition and preserves only complete initialized cells.
- `malloc` and `calloc` assigned to `uint8*` are modeled as positive byte
  extents, with one-byte access ranges and zeroed `calloc` reads; their
  complete ranges can be reclaimed by `free`.
- `malloc`, `calloc`, and bounded `realloc` assigned to `int32**` or `uint8**`
  are modeled as positive pointer-sized ranges, with pointer-cell
  loads/stores, null initialization for `calloc`, prefix preservation, and
  complete `free` reclamation.
- `malloc`, `calloc`, and bounded `realloc` assigned to matching `struct S*`
  are modeled as positive byte extents, with `items[i].field` using the ABI
  struct stride, initialized-field prefix preservation, and complete `free`
  reclamation.
- Arbitrary positive byte extents assigned to supported pointer types are
  modeled as byte-backed allocation authority. `realloc` preserves complete
  initialized cells that fit, rejects out-of-bounds typed accesses, and allows
  complete `free` after a non-divisible resize.
- Multidimensional arrays, initializers, and arrays of structs parse and
  lower to the existing block model with correct byte offsets.
- `scripts/check.sh` passes.

Related: [struct-model.md](struct-model.md);
[integer-types.md](integer-types.md) for `size_t` sizes.
