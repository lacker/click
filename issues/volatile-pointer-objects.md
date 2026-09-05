# Model volatile accesses to pointer-valued objects

Found by the 2026-09-04 MVR audit. The existing small volatile model covers
integer scalar objects and pointers to volatile scalar storage. Linux
`WRITE_ONCE(parent->rb_left, new)` instead performs a volatile access to an
object whose stored value is itself `struct rb_node *`; after macro expansion
the access goes through a pointer to a volatile pointer-valued cell.

This remains a sequential model. Concurrent observations and memory ordering
belong to [concurrency-and-atomics.md](concurrency-and-atomics.md), outside
MVR.

## Violated invariant

Click must retain exactly one ordered access when accepted C performs a
volatile load or store of a pointer value, while preserving the pointer value's
type and provenance. It must not confuse volatility of the pointer object with
volatility of the pointed-to node.

## Intended regression

An unchanged `WRITE_ONCE`-shaped fixture takes the address of a
`struct node *` field, casts it to the appropriate volatile pointer-object
type, and stores a new node pointer exactly once. A paired read returns the
same provenance-carrying pointer. Negative cases distinguish `T * volatile`,
`volatile T *`, and unsupported deeper qualifier shapes.

## Acceptance criteria

- The C type model independently represents a volatile pointer object and a
  pointer to volatile pointee storage.
- Direct and indirect pointer-valued volatile reads and writes retain one
  ordered kernel-certified access event apiece.
- The stored or loaded pointer keeps its struct identity, offset, nullness,
  and allocation provenance.
- Volatile access does not itself grant a memory resource for the pointee.
- Unsupported qualifier depth is rejected precisely.
- The sequential expansion of the rbtree `WRITE_ONCE` stores, focused
  regressions, and `scripts/check.sh` pass.

Related: [volatile-objects.md](volatile-objects.md),
[struct-pointer-indirection.md](struct-pointer-indirection.md), and
[sequential-kernel-access-primitives.md](sequential-kernel-access-primitives.md).
