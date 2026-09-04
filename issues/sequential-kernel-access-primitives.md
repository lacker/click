# Give kernel access primitives a checked sequential projection

Found by the 2026-09-04 MVR audit. Linux rbtree uses `WRITE_ONCE`,
`READ_ONCE`, `likely`/`unlikely`, and `rcu_assign_pointer` through compiler and
RCU headers. MVR deliberately excludes concurrent-reader and memory-ordering
claims, but it still must verify every function's sequential memory safety and
tree transformation without replacing these operations by edited C.

The sequential projection is not a concurrency proof. It must remain visibly
weaker than the future model in
[concurrency-and-atomics.md](concurrency-and-atomics.md).

## Violated invariant

A platform primitive used by accepted source must have an explicit checked
meaning. Click must neither reject unchanged code merely because an operation
is packaged as a kernel primitive nor silently erase volatile accesses,
single-evaluation guarantees, stores, or unsupported concurrency claims.

## Intended regression

An unchanged focused header defines rbtree-shaped `READ_ONCE`, `WRITE_ONCE`,
branch prediction, and pointer-publication operations using the selected
compiler spellings. Under the sequential profile, prove that each access
evaluates its lvalue and value once, emits its ordered event, and performs the
same scalar or pointer-cell memory transition as the source.

A negative regression asks for a release/acquire or concurrent-reader
postcondition and must fail with a diagnostic that says the selected profile
provides sequential semantics only.

## Acceptance criteria

- The selected import/profile maps each supported primitive to documented C0
  operations with original source provenance.
- `READ_ONCE` and `WRITE_ONCE` evaluate arguments exactly once, retain ordered
  volatile-access evidence, and preserve pointer provenance where applicable.
- `likely` and `unlikely` preserve the value and effects of their argument.
- The MVR form of `rcu_assign_pointer` performs and orders its sequential store
  but produces no theorem about other threads, release/acquire behavior, or
  grace periods.
- Contracts and reports label the resulting verification as sequential; a
  concurrent claim cannot consume this evidence.
- The rbtree primitive sites, focused regressions, and `scripts/check.sh`
  pass.

Related: [volatile-objects.md](volatile-objects.md),
[volatile-pointer-objects.md](volatile-pointer-objects.md),
[gnu-c-extensions.md](gnu-c-extensions.md), and
[concurrency-and-atomics.md](concurrency-and-atomics.md).
