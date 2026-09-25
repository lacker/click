# Open issues

Agents must not create new issue files or issue-list entries unless the user
explicitly asks them to. Discovering a problem during other work is not
authorization; report it to the user instead. This applies to bugs, design
gaps, deferred work, and tooling blockers, even when another document
recommends filing an issue.

When requested, use one `.md` file per independent open problem. Each issue
contains a small intended regression, the violated invariant, and acceptance criteria. Delete
an issue when its fix, regression coverage, and documentation land. Do not
leave the only reproduction in an uncommitted example, and do not quarantine
a regression (in `tests/mdtests.rs` or `tests/examples.rs`) without a
corresponding issue here.

Policy lives in the docs, not here: `AGENTS.md` for when tooling failures
block feature work and the user-authorization rule for issue creation, the
[proof-failure triage guide](../docs/concepts/proof-failure-triage.md) for
classifying a failure before filing (including the smart-versus-simple
tactic rule), [Testing Click](../docs/internals/testing.md) for
quarantine, profiling order, and the expansion workflow, and
[Verification Efficiency](../docs/internals/verification-efficiency.md) for
the complexity contract and scaling-regression policy. Proposals without a
failing deterministic curve are not open roadmap items; when the user requests
an issue, scope it narrowly to the evidence.

## P1: before launch (4)

The launch strategy is to complete P1, deliver the minimum viable rbtree
(MVR), and launch publicly with rbtree as the key demo. MVR is the smallest
result that supports a public claim that Click verified the Linux kernel
rbtree implementation. It verifies an unchanged, pinned upstream `lib/rbtree.c`
and the public inline rbtree implementation in `rbtree.h` and
`rbtree_augmented.h`, under one pinned compiler configuration and LP64 target.

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

P1 is the work that has to land before launch. The list is a
dependency marker, not a prescribed implementation order. An unsound rule is
P1 whatever it is about: the claim is worthless if the verifier accepts false
contracts, so soundness bugs come first even when rbtree does not exercise
them. A gap that only a different program would hit is normally P2. The
remaining concurrency and shared-heap milestones are also P1: they check the
architecture before launch while rbtree remains the key demo. The selected
control-flow, byte-representation, arena, and basic C++ milestones have
landed with bounded support claims; broader language, synchronization, and
graph coverage remain P2.

Soundness and kernel shape:

- [Design resource invariants for sequential and concurrent shared heaps](shared-heap-graph-demo.md)

Program import and execution:

- [Verify a concurrency demo with threads, mutexes, and publication](concurrency-demo.md)
- [Verify a pointer-chasing search over an index array](dfs.md)

The completed [basic C++ example](../examples/basic-cpp/README.md) verifies
references, checked scoped cleanup, and a modular caller. The unchanged
Bitcoin Core `MoneyRange` function under its real Clang project profile is
verified in
[`integrations/bitcoin-core-money-range/`](../integrations/bitcoin-core-money-range/).
The first [cross-call exception mdtest](../mdtests/cpp_one_guard_unwind.md)
also verifies one `noexcept` guard constructed inside a `try`: its destructor
restores caller memory before either normal continuation or the matching
`catch` observes it. The selected control-flow demo is now complete through
its two-guard and conditional-lifetime acceptance cases, including a
conditional guard whose normal call outcome continues while the caught outcome
returns, plus hostile cleanup proofs and a deterministic scaling regression.
General backward/irreducible `goto`, multi-compiler support, and broad C++
coverage remain outside the delivered slices. The completed
[byte-representation example](../examples/byte-representation/README.md)
verifies a record's representation copied through a byte buffer and back,
preserving its scalar and pointer identity without granting pointee
authority; its design record is
[Byte representation](../docs/internals/byte-representation.md). The
frozen sequential shared-heap program does not depend on goto or C++. Its
resource-invariant design must also state how a future concurrent
reference-counted version differs from the sequential one.

Specification and proof:

- [Verify the Linux rbtree example on the recursive structure models](rbtree-example.md)

## P2: after launch (25)

- [Make `step` simple across a call precondition](simplify-step.md)
- [Reject `result` inside entry snapshots](result-accepted-in-entry-snapshots.md)
- [Lower a dependent composite argument in every tactic position](dependent-composite-argument-in-tactics.md)

Worth doing, not worth blocking the rbtree claim on. Promote one to P1 when
it turns out to block that claim: if P1 work exposes one of the tooling
failures described in `AGENTS.md`, that issue becomes a blocker under the
normal tooling-first policy and moves up.

C language coverage:

- [Support general backward and irreducible goto](goto.md)
- [Extend static-storage initializers and string-literal coverage](global-variables.md)
- [Import kernel-scale preprocessed translation units](kernel-scale-preprocessing.md)
- [Verify Linux rbtree inline helpers from the pinned headers](linux-rbtree-inline-helpers.md)
- [Transport current static state through cross-file callers](static-state-caller-transport.md)
- [Support multiple C compilers and target ABIs](multiple-compilers.md)
- [Give private static storage sound ownership across helper calls](private-static-helper-ownership.md)
- [Extend bounded control flow](control-flow.md)
- [Resolve linked initializers in their defining file](linked-initializer-private-names.md)
- [Model variadic functions](variadic-functions.md)
- [Model concurrency and atomics](concurrency-and-atomics.md)
- [Model signed eight-bit integers](signed-byte-integers.md)

Semantics and reasoning:

- [Add Euclidean division and remainder for `Integer`](integer-division-and-remainder.md)
- [Extend the resource algebra: fractions, persistent tokens, mutual recursion, symbolic coefficients](resource-algebra-extensions.md)
- [Recursion](recursion.md)

Proof language and tooling:

- [Extend modules and imports beyond the delivered rbtree slice](specification-imports.md)
- [Reduce repeated work in deeply nested `Integer` quantifiers](deep-quantifier-scaling.md)
- [Complete general-purpose algebraic data type support](algebraic-data-types.md)
- [Add a smart tactic for dynamic range framing](dynamic-range-frame.md)
