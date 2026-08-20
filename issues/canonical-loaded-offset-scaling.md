# Canonical loaded offsets need a deterministic scaling curve

## Violated invariant

Canonicalization fixed the recursive load-in-offset failure, but scalability
is part of correctness: adding unrelated snapshots or facts must not restore
superlinear work in the explicit transport used by
`field_derived_precise_effect_after_metadata_write`.

The motivating proof is currently green and healthy. Its old single-corpus
timing is supporting evidence, not a scaling regression, and wall-clock time
cannot establish the required bound.

## Intended regression

Build the same field-derived metadata-write transport at several deterministic
sizes, measure verifier work units for the selected `have`, and assert a
linear-up-to-indexing envelope. Pin the real mdtest's selected operation below
the ordinary tactic budget as a corpus canary.

## Acceptance criteria

- At least three input sizes exercise the same production proof path.
- The curve uses deterministic work units and states its allowed envelope;
  elapsed time is diagnostic only.
- `mdtests/field_derived_precise_effect_after_metadata_write.md` remains green
  without changing C, proof intent, budgets, or limits.
- This file and its Open-list line are deleted when the curve and corpus
  budget regression land under a green `scripts/check.sh`.
