# Keep resource-backed example pipelines on outcome Proof

## Violated invariant

The repository's end-to-end list examples should complete through the same
typed outcome and resource operations as the focused fixtures. They currently
pass only after `outcome simp compatibility construction`, so the migration's
largest vertical examples still cross back into certificate reconstruction.

## Current reproductions

- `examples/linked-list` (`list_roundtrip.ensures_3`)
- `examples/recursive-zero-list` (`zero_list_pipeline.ensures_1`)

The 2026-08-19 census records compatibility construction, but not legacy exit
planning, for both.

## Intended regression

- Attribute each compatibility entry to the first missing typed outcome
  operation before editing; the resulting issue remains this leaf only if both
  examples share that operation or compose already-migrated operations.
- Retain resource folds/observations, recursive call effects, and final
  proposition closure in one proof lineage.
- Expansion and audit run on both complete examples, not a synthetic rewrite
  of their C source.

## Acceptance criteria

- Both examples verify without either outcome fallback span.
- No C source, ownership contract, or recursive structure is weakened to make
  the proof pass.
- The accepted proof exposes a structured certificate without an ordinary
  reconstruction/replay gateway.
- The examples gate and full `scripts/check.sh` pass.

