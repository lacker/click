# Preserve unchanged loads across opaque calls

## Problem

The initial growth proof had to copy `owner->len` into `old_len` and write it
back on both return paths, even though the allocation and copy helpers do not
modify that field. Without the artificial store, opaque-call composition lost
the useful spelling connecting the post-call load to its pre-call value.

This is a proof-model wart. Existing C should not need redundant save/restore
assignments merely to keep an unchanged field recognizable.

## Intended design

When applying an opaque contract, preserve load equalities for memory proven
separate from every mutable effect of the call. The fact may be represented as
a transition/transport certificate, but it must replay using only the callee's
public effect contract and caller separation evidence. Do not expose havoc block
names or rely on search remembering an implementation detail.

Dependent loads need careful handling: preserving `owner->len` is valid when
the address expression and its storage are stable; preserving
`owner->data[i]` additionally requires stability of the pointer, index, and
target range.

## Regression

Use a caller with a struct field adjacent to a resource passed through two
opaque helpers. Prove the field remains equal to `old(owner->field)` without
saving or rewriting it in C. Include a negative case where the callee's mutable
range overlaps the field.

## Acceptance criteria

- Unchanged separated scalar fields retain a public post-call equality.
- The equality has a deterministic surface certificate.
- Overlapping effects do not preserve the load.
- The vector-growth C code needs no redundant `old_len` restoration.
