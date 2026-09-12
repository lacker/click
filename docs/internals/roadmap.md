# Roadmap

Click's current roadmap is to complete the P1 work, verify the Linux kernel
rbtree implementation, and launch publicly with rbtree as the key demo.

The [issue list](https://github.com/lacker/click/blob/master/issues/README.md)
is authoritative for the P1 work and the minimum viable rbtree (MVR) proof
scope. This page describes the launch strategy; it does not maintain a second
feature backlog.

## Complete the P1 work

Work through the open P1 issues in dependency order. P1 means required before
launch, not a prescribed order within the list. Choose the next task by what
unblocks the rbtree proof, and close an issue only when its fix, regression
coverage, and documentation land.

Keep verifier correctness and tooling stability ahead of feature work. A
soundness bug or broken verification, expansion, or diagnostic boundary is a
blocker even if the current rbtree example does not expose it. Follow the
[proof-failure triage](../concepts/proof-failure-triage.md) and
[verification efficiency](verification-efficiency.md) rules.

## Verify rbtree

The launch demo must verify unchanged, pinned upstream rbtree source and its
public inline implementation under the compiler configuration and target
defined by MVR. The exact source boundary and required properties live in the
issue list.

The proof covers sequential memory safety and defined behavior, tree structure,
red-black invariants, node-set and in-order-sequence preservation, traversal,
termination, and modular augmentation callbacks. Contracts, resources, lemmas,
tactics, and verifier improvements must handle the source as written.

Completion requires the full MVR proof and a green `scripts/check.sh` gate.
Passing helper examples or finishing individual P1 issues is progress toward
that result, not a substitute for the complete demo.

## Launch publicly with rbtree

Once P1 and the MVR proof are complete, prepare the public launch around that
result:

- Make the pinned source, build configuration, sidecars, and verification
  instructions easy to find and reproduce.
- Explain the properties Click proves and show how the proof applies to the
  existing rbtree implementation.
- State the demo's scope precisely: sequential behavior under one pinned
  compiler and target, with the documented assumptions. It does not establish
  concurrent RCU correctness or verification of the whole Linux kernel.
- Use rbtree as the central example in the public launch explanation and demo.

## After launch

The P2 list records deferred work. Broader C coverage, additional targets,
concurrency, other library demos, and future program languages such as C++ and
Rust do not add launch prerequisites. Revisit their order after the rbtree
launch. Promote work only when it becomes a launch blocker under the existing
issue-priority and tooling-stability rules.
