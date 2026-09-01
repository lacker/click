# Widen the struct model

Found by the 2026-09-01 kernel audit at cb034b21.

Struct pointers are supported: declarations, `->` field access, and
`malloc(sizeof(struct S))` lower fields to LP64 byte offsets carried as
`CExpression::PointerOffsetBytes` (`src/kernel/primitives.rs:235`,
`docs/internals/kernel.md` "C ABI and memory layout"). The model stops there.
Struct fields may only be `int32` or pointers (`src/languages/c/syntax.rs:847-854`
"struct fields currently support int32 and pointer fields"); struct values
cannot be parameters, locals, or returns (`syntax.rs:961` "only
pointer-to-struct types are supported"); arrays of structs are rejected for
parameters and locals (`syntax.rs:922-926`, `:1129-1133`); embedded structs,
byte buffers in structs, unions, bitfields, enums, and typedefs do not exist.
Kernel-side, `CType` has no struct or union variant (only the
`Int32Array`/`UInt8Array` aggregates) and `CExpression` has no member
operator; everything rides on pointer offsets. `docs/internals/roadmap.md:89-96`
lists struct values, embedded structs, arrays of structs, and unions as
remaining. The pilot target json-c's `json_object` uses unions, enums, and
function pointers.

## Violated invariant

Click should model the aggregate types real C declares, with explicit ABI
layout rules, so that a function over a struct containing a byte buffer, a
nested struct, an enum, or a small union can be verified without rewriting
the declaration.

## Intended regression

Staged mdtests, each with an unchanged C file:

1. A struct with a `uint8` field and a fixed `uint8 buf[16]` field, read and
   written through a pointer.
2. An embedded struct field (`struct inner in;`) accessed as `p->in.x`, and
   an array of structs indexed as `a[i].x`.
3. An `enum` used as a field type and in a comparison.
4. A struct passed and returned by value (copy semantics, no aliasing).
5. A union of `int32` and `int32*` with a tag field, read only through the
   active member.

## Acceptance criteria

- Field types extend to every supported scalar and to fixed arrays, embedded
  structs, and enums; layout follows the documented LP64 rules and is tested
  against `repr(C)`.
- Struct-by-value parameters, locals, and returns are modeled as copies with
  their own local blocks.
- Unions and bitfields are either modeled with explicit rules or rejected with
  a diagnostic that names the unsupported construct; no silent approximation.
- Resource clauses (`owns object(p)`, field ranges) cover the new shapes.
- `scripts/check.sh` passes.

Related: [c-type-spellings.md](c-type-spellings.md) for `typedef`;
[integer-types.md](integer-types.md) for the scalar field types.
