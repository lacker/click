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
