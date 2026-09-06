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
   subset is not yet sufficient as standalone retained proof authority.
   Certification and later core consumers must reuse that retained fact; they
   account for 23 repeated answers in this census.

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

In this issue, these internal objects are **typed kernel evidence retained in
the proof object's checked execution and, after finalization, its resulting
claim**. They are not certificates in the glossary's narrower sense. A
certificate is the surface-expressible explicit proof serialized by expansion;
it has no semantic authority until its operations advance the kernel proof
object. Contract certification is likewise a phase that rechecks retained
execution evidence, not a separate load-equality checker or proof
representation.

Framed atomic transport is not yet migrated. Its remaining direct
`c_memory_load_is_unchanged` call now has typed witnesses for
`StoreExplicitRange` hops, but the selected DAG path can still finish at a
snapshot whose loaded cell agrees with the target only after comparing their
small, bounded snapshot delta. The global prover and its search machinery must
remain until that terminal comparison and the separate incomplete edge route
identified below have typed, locally checkable witnesses.

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

The implemented typed-evidence slice does not introduce a general pointer-in-
range proof language: the two memberships are structural. A typed store-hop
witness retains either the exact proposition or the owning `ResourceContext`,
plus the indexed range pair and its orientation. The composition projection
index retains that shared owner alongside each pair, so evidence collection
does not scan ambient compositions. Checking confirms the named authority,
the composition's ownership separation when applicable, and the two
structural memberships; it does not re-run general resource reasoning.

Typing this hop exposed a distinct endpoint obligation. An initial replacement
probe reported 12 bounded-pool framed-transport queries for which the checked
atomic cell resolver returned no DAG equality but the legacy prover returned
true. That count is stale after the typed store-range slice and intervening
memory-resolution changes: the focused census below observes only one such
bounded-pool query on `ebaca78b`.

### Framed-transport endpoint census (2026-09-05)

A temporary probe compared the checked atomic resolver with the legacy prover
at the last direct framed-transport consumer. For every legacy-only success it
recorded the deciding route, selected derivation endpoint, exact non-local
snapshot delta, and the first successful disjointness rule for each differing
cell. The complete example and mdtest fixture harnesses passed with the probe;
the instrumentation was then removed.

There were nine dynamic legacy-only checks, representing five distinct query
shapes:

| fixture | dynamic checks | legacy route | bounded delta | cell evidence |
|---|---:|---|---:|---|
| `bounded-pool` | 1 | derivation endpoint | 2 | explicit separated ranges |
| `owned-vector` | 2 | root snapshots | 1 | common-base distinctness |
| `copy3_array_demo` first query | 2 | root snapshots | 4 | one common-base and three explicit-range distinctions |
| `copy_n_segment_invariant` | 2 | root snapshots | 1 | common-base distinctness |
| `copy3_array_demo` second query | 2 | incomplete derivation | none | typed resolver stops one edge before the target |

The raw deciding route initially made the first four rows look like one
general snapshot-delta evidence shape. Their construction origins show a more
specific boundary.

### Delta-origin follow-up (2026-09-06)

A second temporary probe traced both endpoint derivation chains and recorded
where a root with no DAG parent was first constructed. None of the six dynamic
root-snapshot checks came from an arbitrary independent reconstruction:

| fixture | origin of the apparent root delta | missing retained evidence |
|---|---|---|
| `owned-vector` | load canonicalization projected one execution snapshot by removing only a local `i` cell | the canonical projection plus the following indexed store's common-base distinctness |
| `copy_n_segment_invariant` | the same canonical projection, again removing only local `i` | the canonical projection plus the following indexed store's common-base distinctness |
| `copy3_array_demo` first query | load canonicalization projected the exact loop snapshot, removing local `i` and three cells at the other separated resource base | the canonical projection, its exact discarded-cell authority, and the following indexed store's common-base distinctness |

`canonicalize_atomic_loads_deep` deliberately interns these restricted
load-observable memories without a derivation. Because equal restricted forms
deduplicate, first-parent DAG provenance would also be insufficient: one
canonical snapshot can be reused for projections of several sources and load
pointers. The canonicalization operation itself knows the source, pointer,
and exact discarded cells when it constructs the form. It should return or
register typed `CanonicalLoadProjection` evidence keyed by that complete
triple, and the proof object's retained load equality should select that exact
projection. This is producer-known provenance, not a claimed arbitrary delta.
Validation must use the retained projection authority rather than rerun the
whole-snapshot canonicalization scan.

The one `bounded-pool` endpoint case is different, but is still structured.
The matching endpoints are two results of the same `CallHavoc` identity and
the same two-range footprint. They were produced from different base
snapshots, and the two-cell delta between the bases is exactly preserved
between the outputs. No individual memory constructor sees both siblings, so
a direct registered pairwise delta is the wrong abstraction. This case needs
typed congruence for the two matching checked call transitions, tied to their
exact call-event authority and base-history/frame evidence. Matching the
numeric havoc variable alone is insufficient because independent
certification can regenerate the same encoding.

Thus the census does **not** justify a general `SnapshotDeltaEvidence` that
lists arbitrary endpoint differences. The next implementation slice should
retain canonical-load projection evidence and finish the common-base store
edge used by the three loop fixtures; those account for six of the seven
dynamic bounded-delta decisions. Re-census after that slice, then handle the
single call-havoc congruence case at its checked execution-event boundary.

The final `copy3_array_demo` row is not an endpoint-comparison obligation. Its
legacy derivation walk reaches the exact target, while the typed resolver
stops at an intermediate node after one checked hop. It needs a separate
edge-justification census; folding it into canonical-projection or call-havoc
evidence would obscure a missing typed path edge.

### Canonical-projection implementation and residual census (2026-09-06)

The canonical-projection/common-base slice is implemented. Atomic-load
canonicalization now registers every exact `(source, projected, pointer)`
triple when it constructs the pointer-observable snapshot. Because several
sources can intern to one projection, the registry retains all triples for
later checking and separately indexes the oldest registered source for
constant-time evidence collection. Retained evidence remains valid if a
better source is registered later. Its check confirms the exact registered
triple and then checks the named memory-DAG walks; it never reruns the
whole-snapshot projection.

The following indexed store now retains either the existing exact inequality
or a named signed-order path proving the written and loaded indices unequal.
The order-path check is linear in those listed premises and performs no
ambient order search. Framed atomic transport asks for this checked evidence
first and retains it on the enclosing checked event, while temporarily
falling back to the legacy prover for the residual cases below.

A fresh complete run of the example and mdtest fixture harnesses initially
reduced the nine dynamic legacy-only checks to three:

| fixture | dynamic residual checks | exact missing evidence |
|---|---:|---|
| `bounded-pool` | 1 | congruence between sibling results of the same checked call transition |
| `copy3_array_demo` | 2 | one store hop whose pointer separation uses general range-membership reasoning |

The six canonical-projection/indexed-store checks are therefore migrated.

The two `copy3` checks are now migrated as well. `StoreSeparatedRanges`
retains a `PointerInRangeEvidence` for both the written and loaded pointer.
The object keeps the old assumption-free structural membership as its cheap
form. When membership is symbolic, it instead names the exact element index
plus independently checked lower and upper bounds. Bounds may be intrinsic
constants or a named signed-order path (including a one-premise path). The one
additional discrete-int32 rule needed by `copy3` retains `k < i + 1` and
`i < 3`; its checker derives `k < 3` directly, using the second strict bound
both for transitivity and to rule out overflow of `i + 1`. Construction first
tries the cheap structural form, then uses the signed-order index; checking is
linear in only the retained path. It never calls
`pointer_in_range_with_width` or the general condition prover.

The symbolic membership form also re-derives the pointer's structural element
index, so changing the pointer, range, element width, or either named order
premise invalidates it. A complete mdtest census now has no legacy framed-load
successes. The complete example census has exactly the existing one in
`bounded-pool`, leaving call-event authority as the only observed endpoint
fallback.

The call-havoc case also reaches a real authority boundary. A call result
retains its `CallHavoc` derivation, fresh variable, write-set identity, and
frozen context, but the proof object has no object naming one checked call
event across the sibling executions being compared. Numeric fresh-variable
equality is deliberately reproducible across independent checking runs, so it
cannot by itself authorize congruence. This case should wait for an explicit
checked-call transition identity (or an equivalent proof-object-owned event
witness), rather than treating two structurally matching havoc markers as the
same event.

Separately, removing `MEMORY_LOAD_EQUALITY_DEPTH_LIMIT` exposes a branching
relation in `owned_string_pipeline.contract`: one `unfold` expands roughly
60,000–120,000 distinct recursive equality subqueries at a maximum active
depth of only six. The roots are registered load variables whose load
addresses themselves contain other registered loads. An exact-query cycle
guard therefore terminates but does not control the branching search. The next
dependent-address evidence must retain the selected congruence/equality paths;
treating two registered load variables as direct atomic DAG queries is
insufficient because their pointers are not structurally equal.

There were no positive fallback decisions in perpetual-service. It remains a
useful negative hot-path fixture: removing the fallback should eliminate its
speculative calls without requiring replacement evidence. Owned-vector also
had only one fresh positive decision in the earlier deciding-route census; the
two identical framed-transport checks in the endpoint census are repeated
uses of the same canonical-projection/store path shape. Its many other probes
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
  on the function-claim proof object. `StoreExplicitRange` now retains and
  checks exact proposition or owned-composition authority. The remaining
  framed-transport census originally found six dynamic checks needing retained
  canonical load-projection evidence plus common-base store evidence, one
  matching call-havoc sibling case, and two repeated checks of a separate
  incomplete typed DAG edge. The canonical projection, common-base store, and
  `copy3` pointer-membership cases are now migrated; the residual complete
  census is one call-havoc check. A general arbitrary snapshot-delta object is
  not required by the observed fixtures.
- A surface tactic (transport, frame, or a completion of the call step)
  advances the proof object with the snapshot-equality fact and its checked
  evidence. When the tactic is smart, expansion serializes corresponding
  surface-expressible operations as its certificate.
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
