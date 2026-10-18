# Full-width Adler migration checkpoint

This branch preserves unfinished work; it is not a complete fix for
`bugs/adler32-spec-states-lengths-only-up-to-int32-max.md`. The canonical
specification remains unchanged. PRs 1509, 1511 and 1513 supply the independently
verified arithmetic and induction prerequisites.

## Approved API and completed investigation

Use `uint64` lengths and `Integer` checksum sums. Weighted-sum coefficients
also use `Integer`, so differences of weights do not wrap. The shared-spec
draft is `adler32-spec.patch`; apply it from the repository root with:

```sh
git apply --unidiff-zero work/adler-full-width-checkpoint/adler32-spec.patch
```

That draft is intentionally incomplete and does not verify as a whole. Its
first eight theorems do verify, independently preserved in
`verified-prefix.click`. The remaining concatenation proofs still contain
signed bridges that must be migrated. The C, Rust, and correspondence clients
have not been widened.

## Exact stopping point

`adler_byte_offset_association` requires composing two symbolic unsigned
pointer offsets. `pointer-sum.click` isolates the missing proof support:

```sh
click verify --trace-proof signed_offset_control work/adler-full-width-checkpoint/pointer-sum.click
click verify --trace-proof symbolic_unsigned_sum work/adler-full-width-checkpoint/pointer-sum.click
click verify work/adler-full-width-checkpoint/verified-prefix.click
```

On a9e8cb05b (which includes upstream b68673d0f), the signed control passes,
the symbolic unsigned case promptly fails at `normalize using`, and all eight
prefix proofs pass. The sum premise is the exact mathematical Integer sum;
a native wrapping equality would not establish the claimed address equality.

The selected comparison reaches
`kernel::reasoning::memory_resolution::pointer_offsets_proven_equal_for_memory_resolution`.
Its unsigned rules do not cover general symbolic sum composition. The relevant
code is unchanged from b68673d0f. `normalize using` documents other scalar
operations as opaque, so this is a proof-support prerequisite for the chosen
API, not a separate documented-behavior bug.

Pointer arithmetic/formation belongs to another task thread. The earlier
original Rust chunk-tail formation failure cleared after PR 1502; this is a
new prerequisite of the widened specification, not a reproduction of that old
failure.

Once support is available, resume the shared specification, then migrate both
program proofs and their correspondence. Verify, expand, and cold-check the
original contracts. Keep native C/Rust code and verifier budgets unchanged.
Keep the length-limit bug open until all of its acceptance criteria pass.
