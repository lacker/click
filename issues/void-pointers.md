# Model object `void *` pointers

Found by the 2026-09-04 MVR audit. C0 rejects `void *`, while Linux rbtree's
generic search helpers accept `const void *key` and pass it to comparison
callbacks. These pointers are opaque object identities at that boundary; the
rbtree implementation does not dereference the key itself.

## Violated invariant

Generic object pointers must preserve pointer identity, nullness, provenance,
and qualification without acquiring an invented element size or permitting an
untyped memory access.

## Intended regression

An unchanged generic lookup helper accepts `const void *key`, forwards it to a
typed callback, compares it with null, and returns it through a compatible
conversion. Negative fixtures attempt arithmetic and direct dereference on
`void *` and use an incompatible function-pointer signature.

## Acceptance criteria

- `void *` and `const void *` are represented as provenance-carrying object
  pointers with no pointee size.
- Supported conversions between object pointers and `void *` preserve the
  exact pointer and qualification; no pointee ownership is created.
- Equality, null checks, assignment, parameter passing, and return are
  supported.
- Dereference and pointer arithmetic remain rejected until a typed conversion
  supplies a modeled object type.
- Function-pointer compatibility and external contracts retain the `void *`
  position and qualifiers.
- The rbtree generic lookup signatures, positive and negative regressions, and
  `scripts/check.sh` pass.

Related: [const-qualified-types.md](const-qualified-types.md) and
[higher-order-callback-contracts.md](higher-order-callback-contracts.md).
