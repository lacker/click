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
