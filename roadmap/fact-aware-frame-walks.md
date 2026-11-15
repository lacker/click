# Remove implicit memory-history searches from checking

Priority: P1.

## Checking boundaries to preserve

Keep these checking boundaries during subsequent removals:

- `CPointerValue::from_read` uses the supplied address and state's O(1)
  `unchanged_bytes_source()` link instead of `resource_tracker::last_same_version_point`.
  The link crosses cache-only observations, not actual writes. Keep
  `LoadedPointer`, its registry, initialization, and lifetime checks separate
  from this work.
- Bounded cell-source checking does not consult `CELL_VERSION_MEMO`, and
  `MemoryDagHopJustification::SameVersion` is removed. Every retained hop
  corresponds to one actual transition. The history-naming cache still has
  other callers; their migration remains separate work.

Preserve `fresh_pointer_read_naming_across_store_history_has_near_linear_total_work`
and `bounded_cell_source_is_independent_of_history_cache`. Neither ordinary
memoization nor a warmed history cache may hide the cost of a cold query.

## Validation for subsequent removals

Run the ordinary fixture corpus, full normal gate (including scaling), and the
named expansion/replay checks below before publishing. Keep the repaired Rust
`recursive-drop`, `generic-stack`, and `generic-container` negative contract
tests reaching their intended refusals. Keep the pointer rejection fixtures
reaching their intended false claims; do not accept prerequisite failures.
No full nightly run is needed.

Statement footprints must include their automatic storage cleanup. Loop-exit
states still name the state before enclosing scope cleanup, so exit facts
can refer to the loop's locals. Preserve both boundaries without searching
back through execution history.

## Preserve the explicit proof route

Use `preserve(...)` to preserve the complete pointer observation across
a separated transition. A numeric word equality alone does not connect pointer
provenance. The saved-word fixture uses `*(slot as (int32 **))` for its complete
eight-byte observation; it does not dereference the observed pointee.

Resource descriptors support `A * B` and `separation::emp`, with explicit
containment and separation laws in `click::separation`. A preserving call whose
mutable frame comes entirely from full-owned resource inputs publishes
`contains(bound, region.footprint)` when there are no additional effects.
Retain the checked caller-side resource identities, not the callee's equivalent
argument expressions. Keep recursive resources opaque and retain the concrete
memory-effect projection alongside the abstract bound.

Consuming calls receive the same bound over their borrowed and consumed inputs;
a produced output does not cancel it. Bounds for non-unit quantities,
construction, runtime effects, and multi-transition regions are outside this
form. Extend only when
a concrete proof needs them, retaining checked producer effects. Do not turn
arbitrary overlapping sequential effects into a separating conjunction.

Keep these expansion/replay checks passing:

- `saved_word_equality_expansion_cold_replay`
- `explicit_pointer_alias_repairs_expand_and_cold_replay`
- `recursive_witness_pointer_preservation_expands_and_cold_replays`
- `recursive_call_resource_bound_is_explicit_and_replays`
- `destructor_footprint_cleanup_expands_and_replays`
- `pointer_rejection_prefixes_expand_and_replay`
- `charon_stack_transport_repairs_expand_and_replay`
- `separation_history_repairs_expand_and_replay`
- `store_index_separation_expands_and_replays` and
  `store_index_separation_variants_expand_and_replay`

The recursive witness proof now selects the call's containment, applies
`separation::separate_restrict`, and preserves the complete pointer read. It needs no
recursive resource unfolding or footprint reasoning in `normalize`.

## Next walks and invariants

Read-side `CellsForgotten` projections and bulk-write preparation remain
separate from scalar-store invalidation. Removing them requires preserving
read spelling and branch-scoped alias reasoning. `read_identity` is not
initialization/lifetime authority. Do not broaden changes into these paths
without a concrete reproduction and design review.

Keep complete-pointer equality and provenance comparison bounded to one
immediate predecessor per endpoint. Retain the repeated-query, adjacent-state,
explicit-composition, and cold-refusal controls in
`src/scaling_tests/kernel/tests/memory_scaling_tests.rs`. Cold histories include
writes to either pointer half; an undecided comparison must refuse equality.
Do not broaden artifact premise authorization into search or resurrect a
copy-evidence index. The copied-aggregate entry repair retains the producer's
exact complete-pointer equations.

## Design and build cycle

1. Isolate the next history traversal with a deterministic scaling regression,
   including cold queries and misses.
2. State the preservation argument with explicit separation, a recorded
   `.footprint`, and `preserve(...)` links. Use the producer's typed
   reads and exact states; do not reconstruct identities or search for
   intermediate states while applying a link.
3. Discuss missing primitives before extending the kernel. Remove the walk
   and repair proofs without changing the C or weakening contracts.
4. Check ordinary proofs and expansion/replay with the search disabled. Keep
   width, provenance, aliasing, partial-overwrite, and freed-cell refusals.

Discovery belongs in budgeted, expandable planning. Applying a certificate
must cost approximately its explicit size, independent of unrelated history.
Coordinate with [Smart tactics](smart-tactics.md) and
[Spellability](../docs/internals/spellability.md). Keep the compact-run store
experiment separate.
