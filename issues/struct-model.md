# Widen the struct model

Found by the 2026-09-01 kernel audit at cb034b21.

Struct pointers are supported: declarations, `->` field access, and
`malloc(sizeof(struct S))` lower fields to LP64 byte offsets carried as
`CExpression::PointerOffsetBytes` (`src/kernel/primitives.rs:235`,
`docs/internals/kernel.md` "C ABI and memory layout"). The first by-value
slice now extends this with copies of scalar, fixed-dimensional scalar-array,
recursively embedded-struct, and fixed-dimensional embedded-struct-array
fields.
Struct fields currently support `int16`, `int32`, `uint8`, `uint16`, `uint32`,
`int64`, `uint64`, fixed scalar arrays, embedded structs, named enum fields,
pointers, named read-only unions, and fixed-dimensional arrays of embedded
structs. Structs whose fields are only `int16`, `int32`, `uint8`, `uint16`,
`uint32`, `int64`, `uint64`, named enum fields,
fixed-dimensional scalar arrays, recursively embedded structs, or
fixed-dimensional arrays of embedded structs can be parameters, locals,
assignments, and returns by value; each operation uses fresh address-backed
storage and copies modeled leaf fields and array cells recursively.
Local arrays of
those supported structs now lower indexed `items[i].field` access with the
complete LP64 stride. One-dimensional function parameters declared as arrays
of those supported structs use the same stride; the kernel represents the
decayed parameter as a byte pointer while retaining the struct layout for
indexing and resource ranges. Fixed one-dimensional `int32` and `uint8` arrays
are preserved as inline field shapes and indexed through their element-width
pointer arithmetic. Embedded fields and fixed-dimensional embedded-struct arrays
are represented as aggregate places during C0 parsing and are lowered to scalar
leaf accesses. Resource clauses may name an embedded aggregate directly; the
surface parser expands that place into typed leaf ranges while preserving each
leaf's field metadata. Direct aggregate loads and copies remain unsupported.
Fixed-dimensional embedded-struct arrays in by-value
containers are flattened row-major to typed leaf fields with each element's
complete ABI stride. Union
members use overlapping layout and read-only typed loads; union writes,
whole-union values, and by-value containers with function pointers or unions
remain rejected. Data-pointer fields in by-value containers are
shallow-copied: the pointer cell is copied, while the pointee remains shared.
Broader struct-value shapes remain. Compiler- or ABI-dependent layout rules
are tracked in [multiple-compilers.md](multiple-compilers.md).
Modeled scalar leaf-field addresses now use the same typed lvalue path as field
loads and stores, so `&p->field`, `&p->inner.field`, and indexed scalar-array
cells preserve allocation provenance and the combined ABI offset. Address-
taking of union members and pointer forms for unsupported scalar widths remain
outside this slice.
Enum fields use an explicit four-byte
`int32` ABI representation, with enumerator values retained in C0 metadata and
lowered as scalar constants in C expressions.
Kernel-side, `CType` has no struct or union variant (only the
`Int32Array`/`UInt8Array` aggregates) and `CExpression` has no member
operator; the surface aggregate-place node is lowered away and everything
rides on pointer offsets. `docs/internals/roadmap.md:89-96`
lists broader struct values and address-taking beyond modeled scalar leaves as
remaining. The first
tagged-union slice is covered by
`mdtests/struct_tagged_union.md`; arbitrary tag-to-member mappings remain an
explicit source-level precondition rather than an inferred rule. The pilot
target json-c's `json_object` uses unions,
enums, and function pointers.

## Violated invariant

Click should model the aggregate types real C declares, with explicit ABI
layout rules, so that a function over a struct containing a byte buffer, a
nested struct, an enum, or a small union can be verified without rewriting
the declaration.

## Intended regression

Staged mdtests, each with an unchanged C file:

1. ~~A struct with a `uint8` field and a fixed `uint8 buf[16]` field, read and
   written through a pointer.~~ Covered by `mdtests/struct_inline_byte_array.md`;
   the field resource uses the array's byte-width shape.
2. ~~An embedded struct field (`struct inner in;`) accessed as `p->in.x`, and
   an array of structs indexed as `a[i].x`.~~ Covered by
   `mdtests/struct_embedded_scalar_field.md`, `mdtests/local_array_of_structs.md`,
   and `mdtests/struct_array_parameter_fields.md`.
3. ~~An `enum` used as a field type and in a comparison.~~ Covered by
   `mdtests/struct_enum_field.md` and the C0 enum metadata and lowering tests.
4. ~~A scalar-only struct passed and returned by value (copy semantics, no
   aliasing).~~ Covered by `mdtests/struct_by_value_scalar_copy.md` and the
   C0/kernel aggregate-layout metadata test. Named enum fields in that shape
   are covered by `mdtests/struct_by_value_enum_copy.md` and
   `mdtests/struct_by_value_array_copy.md`.
5. ~~A union of `int32` and `int32*` with a tag field, read only through the
   active member.~~ Covered by `mdtests/struct_tagged_union.md` and the C0
   union-layout/read-only-boundary tests. Arbitrary tag-to-member mappings are
   still an explicit source-level precondition; C0 does not infer them.
6. ~~An array of embedded structs (`struct inner values[2]` or
   `struct inner values[2][2]`) indexed through a containing struct pointer.~~
   Covered by `mdtests/struct_array_of_embedded_structs.md`,
   `mdtests/struct_multidimensional_embedded_array.md`, and the C0
   ABI/execution tests.
7. ~~A struct containing an embedded struct passed and returned by value,
   with nested updates isolated from the caller.~~ Covered by
   `mdtests/struct_by_value_embedded_copy.md` and the flattened aggregate
   layout test.
8. ~~A struct containing an `int32*` field passed and returned by value, with
   pointer bits copied shallowly and pointee writes remaining shared.~~ Covered
   by `mdtests/struct_by_value_pointer_copy.md` and the C0/kernel aggregate
   metadata and copy tests.
9. ~~A struct containing a fixed-dimensional array of embedded structs passed
   and returned by value, with nested element updates isolated from the
   caller.~~ Covered by
   `mdtests/struct_by_value_embedded_array_copy.md`,
   `mdtests/struct_by_value_embedded_array_multidim_copy.md`, and the flattened
   row-major array-element metadata test.
10. ~~Addresses of direct and nested scalar leaf fields preserve allocation
    provenance and their combined ABI offsets, and pointer stores update the
    selected leaf.~~ Covered by `mdtests/struct_field_address.md` and the C0
    nested-field lowering regression. Unsupported-width address-taking must
    not silently fall back to an `int32*`.
11. ~~Fixed multidimensional `int32` and `uint8` arrays inside structs retain
    their declared shape, flatten indices row-major by element width, and
    survive by-value copies.~~ Covered by
    `mdtests/struct_multidimensional_scalar_array.md` and the C0 shape and
    row-major lowering regressions.
12. ~~Addresses of cells in fixed-dimensional scalar-array fields preserve
    row-major offsets, element width, and allocation provenance, and pointer
    stores update the selected cell.~~ Covered by
    `mdtests/struct_scalar_array_element_address.md` and the C0 indexed-lvalue
    address regressions.
13. ~~Scalar `uint32`, `int64`, and `uint64` fields retain their declared
    types, LP64 offsets, typed leaf loads/stores, and by-value copy semantics.~~
    Covered by `mdtests/struct_wide_scalar_fields.md` and the C0 layout and
    aggregate-copy regressions.
14. ~~Direct `views`, `owns`, `consumes`, and `produces` clauses over embedded
    structs and fixed-dimensional embedded-struct arrays expand into disjoint
    typed leaf ranges, including mixed-width fields.~~ Covered by
    `mdtests/struct_aggregate_resources.md` and the surface metadata regression.

## Acceptance criteria

- Field types extend to every supported scalar, data pointer, fixed arrays,
  embedded structs, and enums; layout follows the documented LP64 rules and is
  tested against `repr(C)`.
- Copyable struct-by-value parameters, locals, assignments, and returns are
  modeled as recursive copies with their own local blocks; leaf field names,
  offsets, and scalar/pointer types remain in flattened aggregate metadata,
  including row-major paths for every fixed-dimensional scalar array and
  embedded-struct array.
- Data-pointer fields in those copies preserve the exact pointer value and
  provenance without copying the pointee or transferring ownership.
- Address-taking of modeled scalar leaf fields preserves the original
  allocation block, adds every ABI field offset in the chain, and returns the
  correct modeled pointer type; unsupported pointer forms are rejected rather
  than approximated.
- Unions are either modeled with explicit rules or rejected with a diagnostic
  that names the unsupported construct; no silent approximation. Other
  compiler-dependent layout constructs are owned by `multiple-compilers.md`.
- Resource clauses (`owns object(p)`, field ranges) cover the new shapes.
- `scripts/check.sh` passes.

Related: [c-type-spellings.md](c-type-spellings.md) for `typedef`;
[integer-types.md](integer-types.md) for the scalar field types.
