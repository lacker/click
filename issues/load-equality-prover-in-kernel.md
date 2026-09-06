# Move the global load-equality prover out of the kernel

`PureFactContext::memory_loads_proven_equal`
(`src/kernel/assumptions/condition_reasoning/memory_conditions.rs`) decides
whether two loads of one cell taken at different memory snapshots denote
the same value. Its cheap legs are checks: fact transport, resolving a load
to a recorded value, the memory DAG's recorded edges, and a direct
snapshot match. Its last leg, `c_memory_load_is_unchanged`, is a prover: it
reconstructs the cell's write history from the effect summaries and
mutates-only facts in scope and frames the loaded pointer across each
intervening effect. Fact matching modulo snapshots
(`conditions_equal_modulo_proven_snapshots`, used by
`proves_condition_exact_or_snapshot` and the decision procedure's fact
scans) calls the decision for every pair of loads a fact and the goal
align, and the framed-load prover's own decisions scan facts again, so the
decision re-enters itself with a branching factor of the number of facts.

The recursion is cut by `MEMORY_LOAD_EQUALITY_DEPTH_LIMIT = 2`
(`src/kernel/assumptions.rs`), which the 2026-09-03 census found met
345,653 times over the examples and 315,061 over the mdtests, marking the
enclosing decisions truncated so the memo layers cannot cache them. It is
the one bound in `issues/simplify-kernel.md` that no counter-free
replacement inside the kernel removes, because it does not bound a walk
over a well-founded structure; it caps a search. Measured on owned-vector
(2026-09-03, `click profile`, master `5baf00cf` as the baseline):

| variant | wall | framed-load walks |
|---|---|---|
| depth of two | 7.5 s | 611 |
| cycle check on the pair | 32 s | 4,733 |
| cycle check and a memo per pair | 28 s | 4,732 |
| nested queries skip the prover | 9.5 s | 138 |

The memo does nothing because the pairs are distinct, which is what a
search produces; the last variant is the depth limit under another name.

## Deciding-route census (2026-09-05)

The follow-up census measured the last-resort
`c_memory_load_is_unchanged` call itself, after every cheaper leg in
`memory_loads_proven_equal` had failed. Temporary counters recorded both the
outer result and the first successful route inside the fallback. The counters
were run with
`cargo test --test examples example_projects -- --nocapture` and
`cargo test --test mdtests mdtests -- --nocapture`, then removed.

| corpus | fallback attempts | decided true | misses |
|---|---:|---:|---:|
| examples | 1,628 | 31 | 1,597 |
| mdtests | 1,347 | 27 | 1,320 |
| total | 2,975 | 58 | 2,917 |

Thus 98.1% of the last-resort calls did not prove anything. The 58 positive
answers came from only four mechanisms. Twenty-three were positive-memo hits,
not independent evidence; the decisions which populated them are included in
the other rows.

| first deciding mechanism | fresh decisions | memo reuses | fixture and consumer |
|---|---:|---:|---|
| canonical snapshot match | 2 | 0 | `copy3.contract` / `simp` (1); `sort3_sorted` verifier core (1) |
| small-snapshot alias check | 13 | 0 | `copy3.contract` / `simp` (8); `fill_tail_old_prefix_segment.contract` / `simp` (5) |
| effect-fact chain | 12 | 0 | `copy3.contract` / `simp` (12) |
| memory-derivation walk | 8 | 23 | the example consumers detailed below |

The example decisions through the memory DAG were:

| fixture and claim/phase | active tactic | fresh DAG decisions | memo reuses | load being transported |
|---|---|---:|---:|---|
| bounded-pool, `pool_pipeline.contract` | `transport` | 1 | 0 | `pool->capacity` across writes to the two objects |
| input-cursor, `input_cursor_shared_pipeline.contract` | `have` | 1 | 0 | shared `data[0]` across mutation of the left cursor |
| owned-split-buffer, `owned_split_buffer_pipeline.contract` | `step` | 1 | 5 | `owner->data` across adjacent call snapshots |
| owned-split-buffer, certification | none | 2 | 6 | the same `owner->data` load, checked again while certifying the result |
| owned-split-buffer, verifier core | none | 0 | 2 | the same already-proved pair, checked again by a core consumer |
| owned-string, `owned_string_pipeline.contract` | `step` | 2 | 8 | `owner->data` across the `pop` call snapshots |
| owned-string, `owned_string_pipeline.contract` | `unfold` | 0 | 2 | the same already-proved pair during resource unfolding |
| owned-vector, `allocated_vector_push.contract` | `have` | 1 | 0 | one old-prefix element load across the grow/push path |

The mdtest loads were `src[k]` across the `copy3` loop, `p[k]` for the
unchanged prefix of `fill_tail`, and indexed `p` loads in the verifier-core
phase of `sort3`. This means the migration has four concrete obligations:

1. Canonical snapshot equality needs no surface search. Hoist that exact,
   assumption-free comparison into the cheap decision path (or represent its
   result as ordinary retained equality evidence) so it never enters the
   framed-load prover.
2. For the 13 small-snapshot decisions, `simp` must emit a pointer-specific
   frame certificate naming the intervening writes and the checked
   disjointness/alias evidence. Its checked result is a recorded equality of
   the two loads, not another request to compare the complete snapshots.
3. For the 12 `copy3` effect-chain decisions, `simp` must select the exact
   sequence of effect-summary or mutates-only facts and emit per-hop framing
   evidence. The kernel checks the named chain linearly and records the
   terminal load equality.
4. For the eight fresh DAG decisions, `step`, `transport`, and `have` must
   retain the selected DAG path with typed justification for every
   assumption-dependent edge. The existing
   `AtomicMemoryLoadEqualityEvidence`/`MemoryDagLoadEqualityEvidence` types are
   the starting point, but their comments correctly note that this typed
   subset is not yet a complete certificate. Certification and later core
   consumers must reuse that retained fact; they account for 23 repeated
   answers in this census.

The first consumer migration landed after this census. Fixed-state restricted
`simp` can now follow its explicit equality rewrites with a snapshot-anchored
surface `transport`; the input-cursor case retains that transport in its
expanded proof and verifies again after parsing. With that bridge in place,
`memory_loads_proven_equal` no longer falls through to
`c_memory_load_is_unchanged`, and both fixture harnesses pass. This removes
global framed-load reconstruction from ordinary fact matching without adding
Click syntax.

This does not complete the issue. The framed-load prover still has direct
kernel consumers in loop checking, resource endpoint comparison, contract
certification, and other proof/certification helpers. The load-equality depth
guard also remains: removing it immediately still makes the surviving
snapshot-resolution routes re-enter and causes the input-cursor regression to
run far past its normal completion time. Those consumers and the reentrant resolution
path need explicit evidence or exact-query guards before the prover and depth
limit can be deleted.

A second migration slice moved all consumers whose answer is already present
in the recorded memory DAG to the explicit equality check. This includes
surface proof matching, load-variable origin matching, loop effects, resource
endpoints, and the ordinary contract certification helpers. It also deletes
the now-unused bounded-snapshot-comparison mode and its conditional reasoning
paths.

The third migration slice establishes ownership for checked load-equality
evidence. Resource rewrites and observations capture each exact checked query
and its canonical or typed memory-DAG witness while the event is constructed,
retain the witness on that event, and recheck it when the event advances its
proof. Contract finalization uses the same scoped capture and retains its
witnesses on the exact `CVerifiedFunctionContractClaim` it mints. The capture
is nested, so a resource event owns its own witnesses rather than duplicating
them on an enclosing contract claim. Contract materialization now uses this
checked route, and `arena` verifies through the new boundary.

Framed atomic transport is not yet migrated. The bounded-pool regression needs
a memory-DAG path containing an assumption-dependent `StoreExplicitRange` hop;
`AtomicMemoryLoadEqualityEvidence::is_fully_typed` correctly rejects that hop,
so replacing the remaining direct `c_memory_load_is_unchanged` call makes
`pool_pipeline.contract` fail at `transport`. The global prover and its search
machinery must remain until that edge has a typed, locally checkable witness.

### `StoreExplicitRange` evidence census (2026-09-05)

A temporary probe made each non-direct framed atomic transport request the
explicit memory-DAG equality that will replace its global-prover call, then
inspected only complete DAG derivations returned by that request. It did not
count unsuccessful candidate paths. Every retained `StoreExplicitRange` hop
had the same proof shape:

- the terminal equality reason was `SameCell(CommonSource)`;
- an indexed `CResourceSeparate` candidate supplied the two disjoint ranges;
  that candidate may be an exact proposition or a projection of an owned
  resource composition; and
- the written and loaded pointers belonged to those ranges by the structural
  `pointer_in_range_shallow` check. None needed fact-graph-derived range
  membership or resource-composition reasoning.

The example harness observed 206 dynamic hops: 24 in `arena`, 36 in
`binary-tree`, 2 in `bounded-pool`, and 144 in `ring-buffer`. Repeated checking
and certification account for many of these dynamic uses; the count measures
consumer demand, not distinct propositions. The mdtest harness observed none.
The unit-test corpus observed 384 more dynamic hops, all with the same shape.
The instrumented unit run disturbed one expansion-output assertion solely
because the temporary diagnostic was captured; that test passed normally with
the probe disabled.

An authority follow-up distinguished direct propositions from composition
projections. All 24 `arena` candidates and all 36 `binary-tree` candidates
were projections; both projects still verified when only direct candidates
were typed. The 96 direct candidates reached while checking `ring-buffer`
were exact proposition facts, and it also verified. Every candidate reached
by the failing `bounded-pool` migration was a composition projection. Thus a
direct-fact-only witness handles incidental cases but not the blocker this
slice exists to remove.

The next coherent certificate slice need not introduce a general pointer-in-
range proof language: the two memberships are always structural. It does need
an explicit authority choice for composition projections. Either the store-hop
witness retains the owning `ResourceContext` and the derived range pair, or the
derived separation index becomes an exact certificate authority in its own
right. The former names the logical premise more directly; the latter makes a
derived cache part of the trusted checking interface. In either design the
checker must use an indexed exact lookup, not scan ambient compositions or
silently re-run general resource reasoning.

Separately, removing `MEMORY_LOAD_EQUALITY_DEPTH_LIMIT` exposes a branching
relation in `owned_string_pipeline.contract`: one `unfold` expands roughly
60,000–120,000 distinct recursive equality subqueries at a maximum active
depth of only six. The roots are registered load variables whose load
addresses themselves contain other registered loads. An exact-query cycle
guard therefore terminates but does not control the branching search. The next
certificate shape must cover both the framed `StoreExplicitRange` hop and
typed congruence/equality-path evidence for dependent load addresses; treating
two registered load variables as direct atomic DAG queries is insufficient
because their pointers are not structurally equal.

There were no positive fallback decisions in perpetual-service. It remains a
useful negative hot-path fixture: removing the fallback should eliminate its
speculative calls without requiring replacement evidence. Owned-vector also
has only the single positive decision listed above, so its many other probes
are likewise evidence for deleting, rather than reproducing, the ambient
search.

## Violated invariant

The kernel checks; it does not search. A kernel decision is decided by
rules whose work is bounded by the inputs they name, and search belongs to
the surface's smart tactics, whose results are certificates the kernel
then checks. Global load equality across snapshots should be decided from
recorded evidence only: exact facts, DAG edges crossed by cheap predicates,
and a snapshot-equality fact a tactic established and recorded. Matching a
fact against a goal modulo snapshots should then be an indexed, evidence-backed
transport or restatement followed by a lookup, with no recursion. It is
contextual reasoning, not canonicalization.

## Intended regression

A proof whose goal mentions a load at a snapshot after a verified call and
whose fact was recorded at the snapshot before it, where the call's effect
summary frames the loaded pointer, should still verify, and it should do so
through a recorded snapshot-equality fact rather than a proof the kernel
runs at match time. A scaling regression should show that matching a goal
against N such facts costs work near-linear in N, with the framed-load
prover never invoked from fact matching. The fixtures in the census tables
must verify unchanged. A negative-path regression should also retain a
representative proof such as perpetual-service and show that failed fact
comparisons do not invoke a framed-load planner.

## Acceptance criteria

- **Complete (2026-09-05):** the census above records, per claim or later
  certification phase, which loads the framed-load prover decided after every
  cheaper leg failed and the exact evidence the surface must record in its
  place.
- **Partial:** fixed-state restricted `simp` retains a snapshot-anchored
  `transport`, and fact matching no longer calls the global framed-load prover.
  The independently re-parsed input-cursor expansion is the regression.
- **Partial:** checked resource events own and recheck any checked equality they
  consume, and contract materialization retains its typed equality witnesses
  on the function-claim proof object. Framed atomic transport still needs typed
  `StoreExplicitRange` evidence before its final direct global-prover call can
  migrate.
- A surface tactic (transport, frame, or a completion of the call step)
  records the snapshot-equality fact the kernel needs, as a checkable
  certificate.
- **Partial:** `memory_loads_proven_equal` no longer has the framed-load
  reconstruction fallback, but framed atomic transport remains a direct
  consumer of that prover. Its dependent-load-address congruence search still
  uses `MEMORY_LOAD_EQUALITY_DEPTH_LIMIT`; replace both remaining routes with
  typed evidence and delete the limit with no counter, depth, or tier in its
  place.
- The scaling regression above lands, both harnesses pass, and the
  `click profile` work units of perpetual-service and owned-vector do not
  rise.
- `issues/simplify-kernel.md` no longer lists the load-equality depth as a
  remaining bound.
