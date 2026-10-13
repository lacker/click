# Roadmap

Click's current roadmap is to complete the P1 work, verify the Linux kernel
rbtree implementation, and launch publicly with rbtree as the key demo.

The [issue list](https://github.com/clicklang/click/blob/master/issues/README.md)
is authoritative for the P1 work and the minimum viable rbtree (MVR) proof
scope. This page describes the launch strategy; it does not maintain a second
feature backlog.

## Complete the P1 work

Work through the open P1 issues in dependency order. P1 means required before
launch, not a prescribed order within the list. Choose the next task by its
dependencies and what it unblocks. P1 includes the explicitly selected
stable-views, basic-C++, concurrency, byte-representation, control-flow, and
shared-heap-graph architecture milestones alongside the rbtree work and the
Bitcoin Core C++ proof. The concurrency demo covers thread ownership,
mutex-protected mutation, and one-shot release/acquire publication. The other
demos exercise object representation copying, C cleanup jumps and narrow C++
exception unwinding, and independently owned parents sharing a child. The
representation-copy demo is implemented; its semantics are recorded in
[Byte representation](byte-representation.md).

The forward goto cleanup dependency and the selected control-flow demo are
implemented; general backward and irreducible jumps remain deferred. The
control-flow slice uses internal exceptional execution outcomes, a closed
exceptional set in the verified function signature, separate outcome-specific
claims, and checked C++ `throw`/matching `catch` cleanup edges. A missing Click
exceptional signature means non-throwing; C++ source that merely omits
`noexcept` does not infer one. Its bounded profile, resource-tracker role,
trust boundary, and deterministic scaling evidence are recorded in the
[architecture note](architecture.md#selected-control-flow-and-c-cleanup-model).
Each milestone keeps a bounded support claim and uses the existing proof
engine with deterministic scaling evidence. Close an issue only when its fix,
regression coverage, and documentation land.

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

## Current rbtree status

The MVR proof is not complete. Do not describe the current result as verifying
the unchanged, pinned `lib/rbtree.c`. As of 2026-10-12 it is exactly this.

Click verifies function bodies copied byte for byte from Linux v6.8.12 (commit
`632428373bea7581869cb05dce40bef0d37793e3`, recorded in
`integrations/linux-rbtree/provenance.json`), not the pinned translation unit:

- `__rb_insert` and `rb_insert_color`, with one general contract
  (`examples/rbtree-insert`).
- `____rb_erase_color` and `__rb_erase_color`, with one general contract over a
  context missing one black level (`examples/rbtree-erase`,
  `examples/rbtree-augmented`).
- `rb_erase` with `__rb_erase_augmented`, through 11 per-case contracts: leaf,
  one-child, immediate-successor, and deeper-successor deletion at any position.
  There is no single general `rb_erase` contract and no theorem that the 11
  preconditions cover every valid input.
- `rb_first`, `rb_last`, `rb_next`, `rb_prev`, `rb_replace_node`, and
  `rb_link_node` (`mdtests/rb_*.md`). `rb_next` and `rb_prev` take
  `struct rb_node *` rather than `const struct rb_node *`.
- `__rb_insert_augmented` and `rb_insert_augmented` with callbacks that write
  nothing, and `rb_erase_augmented` for leaf deletion only.

The proofs establish memory safety and absence of undefined behavior,
termination, red-black validity with a black root, parent-pointer consistency,
and preservation of the in-order sequence of node identities (the tree has no
keys or comparator), with an exact model for erase.

They run under `examples/rbtree-insert/rbtree.h`, a hand-written header that
stands in for `include/linux/rbtree.h`, `rbtree_types.h`, and
`rbtree_augmented.h`. It is trusted, and it differs from upstream:

- `WRITE_ONCE` is a two-line volatile store, without the kernel's
  `compiletime_assert_rwonce_type` checks.
- `rb_set_parent` and `rb_set_parent_color` combine the parent pointer and the
  color bit with `|`; upstream uses `+`. The two agree only because nodes are
  at least 4-byte aligned. `rb_set_parent_color` also takes `int32` rather
  than `int`.
- `rb_parent` is a static inline function; upstream defines it as a macro.
- `likely`, `unlikely`, `__always_inline`, `NULL`, and `true` are simplified.

They assume sequential execution (`WRITE_ONCE` is a plain store; RCU readers
and data races are out of scope), views of the static `dummy_callbacks` table,
and augmentation callbacks with no writable footprint, so augmentation metadata
is not modeled.

Not yet covered: the pinned translation unit itself (Click's C front end does
not yet accept it; see `issues/kernel-scale-preprocessing.md`), the real header
inlines (`issues/linux-rbtree-inline-helpers.md`), augmentation metadata,
non-leaf `rb_erase_augmented`, `rb_next_postorder`, `rb_first_postorder`,
`rb_left_deepest_node`, `rb_replace_node_rcu`, and the `_cached`, `rb_add*`,
and `rb_find*` interfaces.

See [What Click trusts](../concepts/trust.md) for the trusted base these proofs
share with every Click claim.

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
concurrency beyond the selected demo, other library demos, C++ beyond its
selected basic and exception-demo slices, and Rust remain later work. General
goto, type punning, and cyclic-graph reclamation also remain deferred. The
[supporting more languages design](https://github.com/clicklang/click/blob/master/design/supporting-more-languages.md)
records the language sequence and longer-term architecture. Revisit deferred
work after the rbtree launch; the issue list remains authoritative for explicit
priority decisions and tooling blockers.
