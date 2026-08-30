# Owned-vector range-disjointness memo bypass

`click profile examples/owned-vector` verifies, but takes about 22 seconds on
the development build and reports a simple-engine defect. The dominant
repeated operation is framed-load checking across call havoc in
`allocated_vector_push`; this is deterministic kernel work, not smart-tactic
search and not proof-surface complexity.

## Violated invariant

A repeated memory-resolution query in one immutable fact context should pay
for its relevant pointer pair once, up to indexed cache lookup. It must not
rescan the same separation candidates once per memory-DAG edge or contract
claim. In particular, simple checking and kernel contract checking should
remain approximately linear, up to indexing factors, in the explicit proof
and affected execution paths.

## Reproduction

From a clean development build:

```sh
target/debug/click profile examples/owned-vector
```

At commit `2ab1084b`, one representative run reports:

- 21.624 seconds total;
- 14.536 seconds in `allocated_vector_push`;
- 6.123 seconds across 2,049 framed-load memory-derivation walks;
- 5.994 seconds across 1,419 call-havoc edges;
- 4.445 seconds across 55,524 range-membership offset-equality checks;
- 9.509 seconds in contract certification and 9.170 seconds in verifier core.

The profile also flags one 526 ms `close_invariants` in `vector_copy`, but that
is about one second total and is secondary to the repeated call-havoc work.

## Diagnosis

The call-havoc DAG edge in `memory_provenance.rs` invokes
`pointers_disjoint_by_range_memoized` inside
`with_isolated_memory_resolution_fuel`. However,
`resolution_query_memo_id` deliberately returns `None` whenever memory-
resolution fuel is already active. Consequently the operation named and
documented as the memoized DAG-walk range query cannot use its memo at its
only call site.

This looks like a bounded implementation bug. The intended first experiment
is to compute and consult the memo key outside the isolated-fuel scope, while
running only a cache miss under that scope. It changes neither the query nor
its fuel bound. Positive entries remain found evidence; negative entries must
retain the existing derivation-generation and search-truncation guards.

## Intended regressions

1. A focused kernel regression asks the same call-havoc range-disjointness
   question repeatedly in one `PureFactContext` and shows that deterministic
   work after the first query grows by only cache-lookup cost.
2. A multi-size regression grows the number of derivation edges or repeated
   framed loads while holding the relevant pointer pairs fixed. The curve must
   stay approximately linear rather than multiplying edges by separation
   candidate scans.
3. Existing positive and negative memory-DAG tests continue to pin identical
   answers, including negative-cache invalidation after a new derivation and
   refusal to cache a truncated search.
4. `click profile examples/owned-vector` verifies without a simple-engine
   diagnosis and materially reduces the range-membership and call-havoc
   aggregates. Wall time is corroborating evidence, not the regression gate.

## Acceptance criteria

- Memo lookup happens before isolated fuel is armed, and a miss runs with the
  same deterministic 8,000-node cap as today.
- Cached successes contain found evidence from the full bounded query.
- Cached failures remain scoped by memory-DAG generation and are never stored
  after fuel, depth, deadline, or other search truncation.
- The focused semantic tests and deterministic multi-size curve pass.
- The ordinary owned-vector fixture verifies unchanged.
- `scripts/check.sh` passes.
