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
Zero-initialized struct globals and function-local struct statics with
supported scalar leaf fields now use stable typed aggregate storage, including
cross-file `extern` sharing and field-level contract effects. Positional
compile-time scalar and null-pointer initializers now populate those same
objects, with omitted leaves retaining zero initialization. Designated
Const-qualified scalar globals and scalar tables now use read-only backing
blocks and preserve pointer-to-const views across translation units.
Static-storage pointers can now use address constants for declared scalar
objects, array elements, and scalar struct fields, including
cross-translation-unit globals and function-local statics. Subobject addresses
are represented as the containing stable block plus their ABI byte offset.
Const-qualified aggregate globals and function-local aggregate statics now use
read-only backing blocks, preserve their field access across translation units,
and reject field writes. Compatible `extern const` aggregate declarations are
checked against their linked definitions.
Scalar-array designators, multidimensional or incomplete arrays, initialization ordering,
and wider string-literal forms remain unsupported; dynamic or non-literal
initialization remains unsupported as well. Fixed-size one-dimensional arrays
of those aggregates now use one stable ABI-sized block, support nested
positional element initializers, cross-file `extern` sharing, file-scope
`static`, function-local `static`, indexed field access, and field-level
contract effects.
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
for rejecting an unauthorized static-array write, `mdtests/aggregate_static_objects.md`
for zero-initialized cross-file and function-private aggregate state,
`mdtests/aggregate_static_effect.md` for rejecting an unauthorized
aggregate-field write, and `mdtests/initialized_aggregate_static_objects.md`
for initialized cross-file and function-private aggregate state,
`mdtests/initialized_aggregate_static_arrays.md` for initialized aggregate
arrays with cross-file, file-scope-static, and function-local-static storage,
and `mdtests/aggregate_array_static_effect.md` for rejecting an unauthorized
indexed aggregate-array write, and
`mdtests/designated_aggregate_static_objects.md` for designated field and
array-element initialization across external, file-scope-static, and
function-local-static storage, `mdtests/const_aggregate_objects.md` for
const-qualified aggregate arrays across translation units and function-local
static storage, and `mdtests/const_aggregate_write_rejected.md` for rejecting
`mdtests/static_pointer_initializers_cross_file.md`,
`mdtests/static_subobject_pointer_initializers_cross_file.md`, and
`mdtests/static_pointer_initializer_const_discard.md` cover stable address
constants for objects and scalar subobjects plus pointee-const rejection. The three
`string_literals` tests for stable read-only literal storage, call-summary
propagation, and indirect-write rejection.

## Acceptance criteria

- The parser accepts supported scalar file-scope declarations with optional
  literal, null-pointer, or stable object/subobject-address initializers, `extern`
  declarations, and internal-linkage `static`
  definitions, including const-qualified scalar objects and scalar arrays, and
  rejects duplicate or missing external definitions across the source bundle.
- The kernel models each externally linked scalar as one stable global block
  and each file-scope `static` scalar as one stable translation-unit-qualified
  block, materialized at entry with its literal, null, or stable address
  initial value (or zero) and
  shared across that object's function frames.
- The kernel models each fixed-size one-dimensional scalar global as one stable
  array block, initialized element-by-element with omitted values set to zero;
  external definitions are shared across translation units and file-scope
  `static` arrays are translation-unit-private. Const-qualified scalar globals
  and arrays use read-only backing blocks, and pointer-to-const views reject
  stores while preserving reads and provenance.
- The parser accepts zero-initialized, positionally initialized, or designated
  struct globals and function-local struct statics whose layouts contain
  supported scalar leaf fields, links compatible external declarations to one
  definition, and zero-fills omitted leaves. Designated fields use literal
  scalar values and may appear in any order. Const-qualified globals and
  function-local statics are read-only, and `extern` declarations must match
  the definition's const qualifier.
- The kernel materializes each supported aggregate as one stable typed-field
  block, using global linkage or function-qualified static storage, applies
  explicit initializer cells once after zero-filling, and keeps that state
  across calls.
- The parser accepts fixed-size one-dimensional arrays of supported struct
  aggregates at file scope and as function-local statics, requires nested
  element groups, links compatible external declarations to one definition,
  accepts literal `[index] = {...}` element designators, and zero-fills omitted
  fields and elements. Non-literal designators, multidimensional, incomplete,
  and dynamic-initialization forms remain rejected.
- The kernel materializes each aggregate array as one stable byte-addressed
  block with complete ABI element stride, zero-fills every leaf, applies
  explicit initializer cells once, and preserves the block across calls.
- Surface Click can name scalar globals and owning-translation-unit statics in
  `requires`, `ensures`, `mutable`, and resource clauses using their address,
  and `old()` applies to them.
- Surface Click can name aggregate leaf fields in `requires`, `ensures`,
  `mutable`, and resource clauses, with field ranges mapped to their ABI
  offsets and `old()` referring to the entry field value.
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
  global write not named in `mutable` is rejected. Aggregate-array indexed
  fields use the same ABI offsets and effect checks. String literals remain
  read-only through copied pointers; automatic/local aggregate designators,
  scalar-array designators, non-literal designators, const-qualified automatic
  aggregate locals,
  multidimensional/incomplete arrays, dynamic or
  non-literal initialization, initialization ordering, and wider literal forms
  remain open.
- `scripts/check.sh` passes.

Related: [multi-function-files-and-headers.md](multi-function-files-and-headers.md).
