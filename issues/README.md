# Open issues

One `.md` file per independent open problem. Each issue contains a small
intended regression, the violated invariant, and acceptance criteria. Delete
an issue when its fix, regression coverage, and documentation land. Do not
leave the only reproduction in an uncommitted example, and do not quarantine
a regression (in `tests/mdtests.rs` or `tests/examples.rs`) without a
corresponding issue here.

Policy lives in the docs, not here: `AGENTS.md` for when tooling failures
block feature work and what always warrants an issue, the
[proof-failure triage guide](../docs/concepts/proof-failure-triage.md) for
classifying a failure before filing (including the smart-versus-simple
tactic rule), [Testing Click](../docs/internals/testing.md) for
quarantine, profiling order, and the expansion workflow, and
[Verification Efficiency](../docs/internals/verification-efficiency.md) for
the complexity contract and scaling-regression policy. Proposals without a
failing deterministic curve are not open roadmap items; file a narrow issue
when evidence exposes one.

## Minimum viable rbtree (MVR)

MVR is the smallest result that supports a public claim that Click verified
the Linux kernel rbtree implementation. It verifies an unchanged, pinned
upstream `lib/rbtree.c` and the public inline rbtree implementation in
`rbtree.h` and `rbtree_augmented.h`, under one pinned compiler configuration
and LP64 target.

The proof must establish sequential memory safety and defined behavior;
parent/child consistency and acyclicity; preservation of the red-black color
and black-height invariants by insertion and erasure; preservation of the
exact node set and in-order sequence by rotations, insertion, erasure, and
replacement; correct traversal results; termination of finite-tree traversal
and rebalancing loops; and modular correctness for caller-supplied augmentation
callbacks.

MVR checks the sequential store effect of `WRITE_ONCE`, `READ_ONCE`, and
`rcu_assign_pointer`, but makes no claim about concurrent readers, atomic
ordering, RCU grace periods, or data races. Those belong to
[concurrency-and-atomics.md](concurrency-and-atomics.md). MVR also fixes one
compiler/target profile; cross-compiler and cross-architecture verification
belongs to [multiple-compilers.md](multiple-compilers.md).

The following open issues are required for MVR. This is a dependency marker,
not a prescribed implementation order:

C import and execution:

- [Accept multi-function files, prototypes, and includes](multi-function-files-and-headers.md)
- [Import kernel-scale preprocessed translation units](kernel-scale-preprocessing.md)
- [Verify inline function definitions reached through headers](inline-functions-in-headers.md)
- [Model the GNU C expression and declaration forms used by rbtree](gnu-c-extensions.md)
- [Model C `_Bool` and `bool`](c-bool.md)
- [Preserve `const` qualification in C types](const-qualified-types.md)
- [Model object `void *` pointers](void-pointers.md)
- [Support pointer-to-pointer forms for struct pointers](struct-pointer-indirection.md)
- [Verify provenance-preserving pointer/integer tagging](pointer-integer-casts-and-tagging.md)
- [Widen the struct model](struct-model.md)
- [Model file-scope objects, statics, and string literals](global-variables.md)
- [Model sequential scalar and pointer-qualified volatile objects](volatile-objects.md)
- [Model volatile accesses to pointer-valued objects](volatile-pointer-objects.md)
- [Give kernel access primitives a checked sequential projection](sequential-kernel-access-primitives.md)

Specification and proof:

- [Offer unbounded integers on the specification side](mathematical-integers-in-specs.md)
- [Add a specification sequence type](sequence-type.md)
- [Give function-pointer parameters checked callback contracts](higher-order-callback-contracts.md)
- [Add abstract summaries for recursive memory structures](recursive-structure-models.md)
- [Prove loop termination from recursive structure descent](structural-loop-termination.md)

An existing architecture issue is not an MVR dependency merely because a
large rbtree proof might exercise it. If MVR work exposes one of the tooling
failures described in `AGENTS.md`, that issue becomes a blocker under the
normal tooling-first policy and should then be added to this list.

## Architecture issues: 4

- [Remove search, fuel, and fallbacks from the kernel](simplify-kernel.md)
- [Make `arithmetic` a smart tactic with an explicit certificate](arithmetic.md)
- [Move the global load-equality prover out of the kernel](load-equality-prover-in-kernel.md)
- [Verify user-defined arena region ownership](arena-resource-ownership.md)

## Functionality gaps: 25

C language coverage:

- [Support multiple C compilers and target ABIs](multiple-compilers.md)
- [Widen the struct model](struct-model.md)
- [Accept multi-function files, prototypes, and includes](multi-function-files-and-headers.md)
- [Model file-scope objects, statics, and string literals](global-variables.md)
- [Model forward and backward goto edges](goto.md)
- [Model variadic functions](variadic-functions.md)
- [Model sequential scalar and pointer-qualified volatile objects](volatile-objects.md)
- [Model volatile accesses to pointer-valued objects](volatile-pointer-objects.md)
- [Model concurrency and atomics](concurrency-and-atomics.md)
- [Import kernel-scale preprocessed translation units](kernel-scale-preprocessing.md)
- [Verify inline function definitions reached through headers](inline-functions-in-headers.md)
- [Model the GNU C expression and declaration forms used by rbtree](gnu-c-extensions.md)
- [Preserve `const` qualification in C types](const-qualified-types.md)
- [Model C `_Bool` and `bool`](c-bool.md)
- [Model object `void *` pointers](void-pointers.md)
- [Support pointer-to-pointer forms for struct pointers](struct-pointer-indirection.md)
- [Verify provenance-preserving pointer/integer tagging](pointer-integer-casts-and-tagging.md)

Semantics and reasoning:

- [Extend the resource algebra: fractions, persistent tokens, mutual recursion, symbolic coefficients](resource-algebra-extensions.md)
- [Offer unbounded integers on the specification side](mathematical-integers-in-specs.md)
- [Add a specification sequence type](sequence-type.md)
- [Give function-pointer parameters checked callback contracts](higher-order-callback-contracts.md)
- [Add abstract summaries for recursive memory structures](recursive-structure-models.md)
- [Give kernel access primitives a checked sequential projection](sequential-kernel-access-primitives.md)

Proof language and tooling:

- [Add a smart tactic for dynamic range framing](dynamic-range-frame.md)
- [Prove loop termination from recursive structure descent](structural-loop-termination.md)

## Hard bucket: 1

- [Recursion](recursion.md)
