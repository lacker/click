# Explicit derivation performs context-wide minimization and contradiction scans

Proof-producing atomic reasoning currently minimizes condition premises by
removing each candidate and rerunning the prover. Loadability reasoning may try
individual candidates and candidate pairs. General failure fallback scans all
conditions for contradictions, including an explicit all-pairs comparison,
and condition proof can scan every proposition and quantified fact.

These algorithms can be reached while checking a simple named rule. Bounded
fuel prevents an unbounded search, but it does not provide the required
codebase-scaling bound.

## Required design

Theory decisions must return proof provenance as they decide the result:
selected graph edges for order reasoning, selected interval/range authority for
memory reasoning, and explicit conflicting facts for contradiction. Maintain
incremental indexes for exact opposites, equality classes, order adjacency,
and quantified conclusions. Certificate construction should consume this
provenance rather than rediscover a small premise set through deletion.

Do not weaken certificates by retaining the entire ambient context. The goal is
small proof evidence produced by the decision procedure in one pass.

## Regression design

Hold one fixed arithmetic equality, contradiction, loadability consequence,
and quantified implication while adding unrelated facts of every other kind.
Measure both decision and derivation construction. Add explicit long-path
order cases whose cost is proportional to the returned path.

Scaling axis: `exact_contradiction_lookup_scales_near_linearly` holds one
contradiction fixed while growing unrelated condition facts. The issue closes
when corresponding fixed arithmetic, loadability, quantified-match, and
long-order-path curves cover their named decision/derivation operation spans.

## Acceptance criteria

- Atomic derivation does not rerun the prover once per ambient premise.
- Contradiction lookup is indexed; it has no all-pairs fallback.
- Quantified matching uses a conclusion/trigger index rather than all facts.
- Returned derivations retain only actual dependencies.
- Fixed derivations pass the fact-count scaling gate.

## 2026-08-13 progress

Contradiction checking now builds canonical indexes for exact
equality/disequality pairs and directed order edges while it performs its
single condition-fact pass. Exact opposite equalities, strict self-edges,
reverse order edges, and equality-versus-strict-order conflicts return from
those indexes instead of entering the nested theory scans. A four-size
deterministic regression holds one exact contradiction fixed while growing
unrelated conditions.

The deeper fallback remains for terms that are equal only through derived
theory facts. Closing this issue still requires provenance-producing order and
loadability decisions, indexed quantified matching, and removal of that
non-structural all-pairs fallback rather than weakening its conclusions.

Signed interval reconstruction now maintains an exact endpoint-to-bound index
incrementally with `Assumptions`. A fixed overflow decision with 128 unrelated
order facts is guarded to use no context-scan fallback. Successful interval
results are also memoized by fact-set content and term, so nested additions
reuse their operands' ranges. Snapshot-equivalent and resolved-load bounds
still use the broader fallback when exact endpoint bounds are insufficient;
indexing those derived order edges remains part of the open provenance work.

Whole-context inconsistency results are now memoized under the enclosing
assumptions identity and DAG-bridging mode. Positive contradictions remain
valid; negative results are scoped to the memory-derivation generation and
excluded after deadline or search truncation. This is not a replacement for
the remaining all-pairs fallback, but it prevents one proof-branch routing
decision from recomputing that fallback hundreds of times over an unchanged
context. A deterministic regression requires the second query not to perform
another full context scan.

Owned-vector's remaining resource entailment also isolates 28 unique
`range_covered_by_fact_range` fallbacks totaling about 0.4s. These are not
duplicate memo hits: their final endpoint/order proof is individually broad.
The open derivation work must index or directly derive those local range
relations; a cache keyed by complete range terms would only hide the scan and
violate the stable-identity requirement.

Concrete pointer-offset arithmetic now precedes proof-aware pointer equality
inside fact-range coverage. This removes a large avoidable derivation subtree
without changing the symbolic case: symbolic offsets retain the existing
snapshot-aware canonicalizer because owned-string depends on it. A focused
counter regression proves the constant shifted-range case performs no
proof-aware pointer-index query.

Attribution inside whole-context inconsistency found that its residual cost is
the non-structural order-conflict fallback: an owned-vector run issued about
31,000 equality-graph endpoint comparisons and 28,000 deeper theory-equality
comparisons from the all-pairs loop. Equality-graph comparisons now use the
shared adjacency index instead of rescanning the complete condition map, and
ordinary variable/constant pairs skip theories that cannot relate their
constructors. This reduced context-inconsistency time from about 0.28s to
0.25s and a current project profile from about 4.96s to 4.88s. The all-pairs
order loop and its roughly 22,000 remaining theory comparisons are still open;
closing them requires the indexed order/equality provenance described above.

The all-pairs order loop is now closed. Labelling the equality graph's
connected components turns every structural endpoint comparison into class
identity: a strict edge inside one class contradicts the equality chain that
built it, and a reverse edge between two classes contradicts this one when
either edge is strict. This subsumes the former single-equal-fact bridge check,
because a class relates endpoints through the whole chain rather than one fact.
Only components an order fact actually mentions are labelled, so the pass
visits what the pairwise comparisons used to reach and no more.

Endpoints that a non-structural theory could relate — a memory load, an
addition, or two conditionals or folds — keep the pairwise comparison, so no
conclusion is weakened. `consistent_order_context_scales_near_linearly` holds a
consistent order context while growing its unrelated facts: deterministic work
fell from N^2 + 2N to 3N, or 16640 units to 384 at 128 facts. Measured on
examples/bounded-pool over three runs each, this is neutral on wall time
(pool_pipeline smart 1.18s before, 1.17s after).

## 2026-08-13 measurement: the premise-rerun criterion has no failing curve

`search_condition_derivation` still literally reruns the prover once per
candidate and then once per candidate pair, but instrumenting it shows that is
not a demonstrated asymptotic violation:

- across the complete `examples` corpus it is entered 120 times with 696
  candidates in total, and the largest single candidate set is 7;
- `examples/owned-vector` and `examples/binary-tree`, the two large integration
  workloads, never enter it at all; and
- growing a function's unrelated ambient conditions from 4 to 32 under
  `execute()` does not enter it either, because the overflow obligation is
  discharged by interval reasoning rather than condition-certificate search.

A theorem-level order goal reaches its premises through
`minimize_derivation_premises`, a binary-search reduction over the premises the
derivation already returned, not through this scan.
`transitive_order_derivation_scales_near_linearly_with_unrelated_conditions`
guards that path and passes as written.

## 2026-08-13 measurement: the non-structural fallback is cheap and untested

Instrumenting the pairwise comparison that context inconsistency retains for
theory-relatable endpoints gives, per project: owned-vector 75 entries with at
most 89 theory-capable order facts and about 25,700 pair comparisons;
owned-string 246; binary-tree none. That is the residual the entry above
predicted, so the count is real.

Its cost is not. Disabling the comparison entirely — an unsound oracle that
bounds what any index could save, since a real index still has to be built and
queried — moves owned-vector from about 7.35s to about 6.6s on a debug build,
roughly ten percent, and the project still verifies. The profiler continues to
classify the run as healthy volume with no operation crossing a bound.

More important, the complete suite passes with that comparison removed. The
fallback therefore had no regression coverage at all: nothing demonstrated a
contradiction that only it can find, so both indexing it and removing it were
unguarded changes.

`derived_order_contradiction_uses_theory_equal_endpoints` now pins it. `x + y`
and `y + x` are related only by additive theory equality, never by an
equality-graph edge, so `x + y < middle` and `middle < y + x` contradict only
through this path. The test fails when the comparison is disabled and passes
with it, so it constrains the fallback rather than merely covering it.

Anyone resuming should treat the ten percent bound as the budget for this work
and extend the pin first: a memory-load case and a fold case would fix the
other theory rules the fallback exists for, and no index or removal should land
without them.

Under the issue policy in `README.md`, the premise-rerun criterion therefore
needs a failing deterministic curve before it justifies provenance machinery. The candidate set
is bounded by the `ConditionIs` facts in one available slice and is guarded by
`check_condition_search_budget`. Anyone resuming should either exhibit a curve
where that candidate set grows with project size, or narrow the criterion to
the paths that remain demonstrably open: indexed quantified matching,
provenance-producing loadability decisions, and the non-structural all-pairs
fallback for terms equal only through derived theory facts.
