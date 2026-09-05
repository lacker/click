# Preserve `const` qualification in C types

Found by the 2026-09-04 MVR audit. C0 does not currently model `const`, while
the Linux rbtree API uses `const struct rb_node *`,
`const struct rb_root *`, and pointers to `const struct rb_augment_callbacks`.
Several functions cast away qualification only when returning an existing
node pointer.

## Violated invariant

Type qualification in accepted C must constrain writes through the qualified
lvalue and survive declarations, typedefs, fields, parameters, casts, and
pointer indirection. Click must not accept writes that the C type system
forbids or treat qualification-only casts as arbitrary pointer conversions.

## Intended regression

An unchanged C fixture traverses a small struct through a pointer to const,
returns one member pointer with an explicit qualification-removing cast, and
never writes through the const view. A negative fixture attempts a direct and
an indirect write through the const-qualified pointer and is rejected.

## Acceptance criteria

- The parser represents top-level and pointee `const` independently through
  the pointer depths supported by C0.
- Loads, address-taking, field access, calls, and compatible qualification
  conversions preserve that metadata.
- Stores through a const-qualified lvalue are rejected before proof search.
- Explicit casts that remove `const` preserve pointer identity and provenance
  and do not authorize mutation without an ordinary mutable resource.
- Function declarations and definitions diagnose incompatible qualifiers.
- The rbtree const signatures, focused regressions, and `scripts/check.sh`
  pass.

Related: [pointer-integer-casts-and-tagging.md](pointer-integer-casts-and-tagging.md).
