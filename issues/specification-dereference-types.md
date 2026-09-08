# Specification dereferences must preserve pointee types

## Invariant

For a typed scalar pointer, specification expressions `*p` and `p[0]` must
load the same type and honor the same `old` snapshot. C fragment lowering
currently gives the generic `CExpression::Load` an int32 result type.

## Intended regression

Keep this C unchanged:

```c
unsigned int bump(unsigned int *p) { *p += 1; return *p; }
```

With `requires loadable(p[0..1])`, `consumes p[0..1]`, and
`produces p[0..1]`, the postcondition `p[0] == old(p[0]) + 1u32` verifies.
The equivalent `*p == old(*p) + 1u32` does not: diagnostics show the old
and current loads failing to establish the update.

## Acceptance criteria

- Lower specification dereferences using the pointer's declared pointee type
  while retaining explicit old/current memory selection.
- Cover uint32 and uint64 pointers, matching indexed specifications, and
  negative wrong-snapshot claims; preserve pointer-origin lowering.
- Ordinary verification and expansion/reverification agree, and
  `scripts/check.sh` passes. Do not rewrite the C to avoid dereferencing.
