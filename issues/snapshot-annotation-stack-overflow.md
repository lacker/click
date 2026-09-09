# Keep deep snapshot-annotation rejection below the native stack limit

**Observed failure.** The existing regression for the snapshot-annotation
structural depth bound aborts the test process with a native stack overflow
instead of returning the expected bounded diagnostic.

**Reproduction.** From the repository root, run:

```sh
cargo nextest run -E 'test(snapshot_annotation_rejects_deep_logic_without_using_the_native_stack)'
```

The test `surface::proof::certificate_tests::snapshot_annotation_rejects_deep_logic_without_using_the_native_stack`
currently exits with `SIGABRT` after reporting `has overflowed its stack`, on
both the clean primary checkout and ordinary task worktrees.

**Violated invariant.** The snapshot annotation depth limit must reject an
overly deep proposition with a source-level diagnostic without exhausting the
native stack.

**Acceptance criteria.**

- The focused regression returns its expected structural-depth error instead
  of aborting.
- `scripts/check.sh` completes successfully with the regression enabled.
- The implementation keeps the depth bound enforced before recursive work can
  exhaust the native stack.
