# Owned-vector call-havoc crossing cache

`click profile examples/owned-vector` verifies, but takes about 22 seconds on
the development build and reports a simple-engine defect. The dominant
repeated operation is framed-load checking across call havoc in
`allocated_vector_push`; this is deterministic kernel work, not smart-tactic
search and not proof-surface complexity.

## Violated invariant

Checking whether one cell survived one immutable call-havoc edge in one fact
context should cost once per relevant `(edge, pointer, fact context)` tuple,
up to indexed cache lookup. It must not rescan the same separation candidates
for every enclosing memory-DAG walk or contract claim.

## Reproduction

From a clean development build:

```sh
target/debug/click profile examples/owned-vector
```

Representative runs at commit `cf0746f5` report 21.6--22.2 seconds total,
including:

- 14.5--16.5 seconds in `allocated_vector_push`;
- about 6 seconds across 2,049 framed-load memory-derivation walks;
- about 6 seconds across 1,419 call-havoc edges;
- 4.4--5.1 seconds across 55,524 range-membership offset-equality checks;
- about 10 seconds in contract certification and 8--9 seconds in verifier
  core.

The profile also flags the two checks of one `close_invariants` source site in
`vector_copy` at about 0.5--0.6 seconds each. That secondary simple-checker
tail is not the dominant owned-vector cost.

## Diagnostic experiments

Two narrower hypotheses were tested and rejected without landing code:

1. `pointers_disjoint_by_range_memoized` was called inside an isolated fuel
   scope that disabled its memo. Moving the fuel scope inside the cache miss
   fixed a focused repeated-query curve, but changed neither the 55,524 hot
   comparisons nor owned-vector wall time. The operation has only 18 dynamic
   calls here and belongs to store-edge crossing, not the hot call-havoc arm.
2. Trying the call-havoc edge's existing frozen-context cache before the
   current proof context made the verifier slower and caused the 30-second
   profile deadline to fire. The current proof context can provide a cheaper
   or stronger framing answer than reconstructing it from the edge's frozen
   context, so reordering the disjunction is not a fix.

The remaining repeated work is in `memory_derivations_reach`: its `CallHavoc`
arm calls `ranges_proven_disjoint_from_pointer_for_frame` against the current
`PureFactContext` for each walk. The existing `FROZEN_CROSSING_MEMO` cannot
cache that answer because it deliberately omits current assumptions from its
key.

## Proposed next experiment

Add a separate current-context call-havoc crossing cache keyed by the interned
derived edge, pointer, stable fact-context identity, and any ambient mode that
can affect the answer. This is a kernel cache design, not a surface or semantic
change.

Positive entries are found evidence. Negative entries must be scoped by the
memory-derivation generation and must not be stored after fuel, depth,
deadline, or other search truncation. The existing unchanged-load and
resolution-query memos provide the safety pattern, but the new key must be
audited against every ambient flag read by the range/frame prover.

## Intended regressions

1. Construct several later snapshots whose derivation walks all cross the
   same call-havoc edge at the same pointer in one fact context. A multi-size
   deterministic curve must show one substantive range check plus indexed
   cache lookups, rather than one separation scan per walk.
2. The same edge and pointer under two distinct fact contexts must not share
   an answer.
3. Adding a derivation that changes a formerly negative answer must invalidate
   the negative entry.
4. Fuel-, depth-, deadline-, or cycle-truncated failures must never enter the
   negative cache.
5. Existing positive and negative memory-DAG tests continue to pin identical
   answers.
6. `click profile examples/owned-vector` materially reduces the call-havoc and
   range-membership aggregates. Wall time is corroborating evidence, not the
   regression gate.

## Acceptance criteria

- The new memo key contains every stable input on which the checked crossing
  answer depends, without deep-hashing the fact context per query.
- Cache hits do not rerun range membership or resource-composition reasoning.
- Positive and negative cache safety follows the constraints above.
- The ordinary owned-vector fixture verifies unchanged and no proof or C
  surface is modified.
- The deterministic multi-size regression passes.
- `scripts/check.sh` passes.
