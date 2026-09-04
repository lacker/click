# Model file-scope objects, statics, and string literals

Found by the 2026-09-01 kernel audit at cb034b21.

The scalar file-scope slice is now implemented for both externally linked and
internal-linkage objects: supported integer globals, compatible `extern`
declarations, exactly one linked external definition, per-translation-unit
file-scope `static` storage, literal or zero initialization, shared storage
across calls, `old(global)`, and one-cell contract footprints. Fixed-size
one-dimensional scalar arrays now use the same stable linkage and
element-initialization model. Function-local scalar `static` objects and
fixed-size one-dimensional scalar `static` arrays are also initialized once
per program state with stable function-qualified storage.
Basic ASCII C string literals are now lowered to function-owned,
NUL-terminated, read-only `uint8` storage and remain stable through calls.
Aggregate globals/statics, multidimensional or incomplete arrays,
initialization ordering, and wider string-literal forms remain unsupported;
dynamic or non-literal initialization remains unsupported as well.
The `cstr` predicate layer still exists only on the spec side over uint8
buffers.

## Violated invariant

Click should model every supported object with static storage duration as
memory that exists at function entry, with contracts able to name it in
footprints and postconditions, so that real C that keeps state in globals or
function-local persistent state can be verified.

## Intended regression

The landed regressions are `mdtests/file_scope_globals.md` for
cross-translation-unit external state, `mdtests/file_scope_static_globals.md`
for independent internal-linkage state, `mdtests/static_scalar_locals.md` for
one-time function-local static storage, `mdtests/file_scope_global_arrays.md`
and `mdtests/file_scope_global_arrays_cross_file.md` for initialized arrays and
cross-file `extern` storage, `mdtests/file_scope_static_arrays.md` for private
array storage, `mdtests/global_effect_requires_mutable.md` for effect
certification, `mdtests/static_local_arrays.md` for one-time function-local
static array storage and indexed effects, `mdtests/static_array_local_effect.md`
for rejecting an unauthorized static-array write, and the three
`string_literals` tests for stable read-only literal storage, call-summary
propagation, and indirect-write rejection.

## Acceptance criteria

- The parser accepts supported scalar file-scope declarations with optional
  literal initializers, `extern` declarations, and internal-linkage `static`
  definitions, and rejects duplicate or missing external definitions across
  the source bundle.
- The kernel models each externally linked scalar as one stable global block
  and each file-scope `static` scalar as one stable translation-unit-qualified
  block, materialized at entry with its literal initial value or zero and
  shared across that object's function frames.
- The kernel models each fixed-size one-dimensional scalar global as one stable
  array block, initialized element-by-element with omitted values set to zero;
  external definitions are shared across translation units and file-scope
  `static` arrays are translation-unit-private.
- Surface Click can name scalar globals and owning-translation-unit statics in
  `requires`, `ensures`, `mutable`, and resource clauses using their address,
  and `old()` applies to them.
- A function-local scalar `static` has one function-qualified memory block,
  is initialized only when that block first enters the state, remains shared
  across recursive/nested calls, and is nameable by its owning function's
  contracts.
- A function-local fixed-size one-dimensional array of a supported scalar type
  has one function-qualified memory block, is initialized element-by-element
  with omitted entries zero-filled, remains shared across recursive/nested
  calls, and is nameable by indexed contract ranges.
- Effect certification treats scalar global and file-scope static writes like
  any other footprint write, and function-local static writes require the same
  explicit footprint. Array elements use ordinary indexed memory ranges, and a
  global write not named in `mutable` is rejected. String literals remain
  read-only through copied pointers; aggregate static storage,
  multidimensional/incomplete arrays, dynamic or non-literal initialization,
  initialization ordering, and wider literal forms remain open.
- `scripts/check.sh` passes.

Related: [multi-function-files-and-headers.md](multi-function-files-and-headers.md).
