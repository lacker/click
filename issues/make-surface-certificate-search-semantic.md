# Make surface-certificate search semantic and bounded

## Problem

Certificate reconstruction can generate a cross-product of `old(...)` and
`at(...)` variants for comparisons nested under quantifiers, implications, and
predicate calls. In a proof with many recorded program points, Click spent
seconds constructing spellings for an internal fact that had no usable source
spelling.

An experimental repair truncated the final candidate list after eight
variants. That number is arbitrary and candidate-order dependent: the first
valid replayable spelling may occur later, so truncation can turn a provable
result into a failure. Arbitrary candidate caps are not an acceptable proof or
performance boundary.

## Intended regressions

Add focused unit and mdtest coverage for a quantified comparison or predicate
fact with many recorded program points:

- one case where the only replayable surface spelling corresponds to a late
  program point;
- one case where no replayable spelling exists; and
- one case with nested conjunction, implication, and quantification that used
  to create a candidate cross-product.

The successful case must produce a certificate that replays after expansion.
The unsuccessful cases must stop within the smart-tactic budget and report a
concise search-exhaustion diagnostic rather than a kernel-state dump.

## Design direction

Index candidate spellings by the memory snapshot markers and program-point
states referenced by the kernel fact. Try structurally compatible recorded
spellings first. Any fallback should use an explicit work budget that reports
exhaustion, while preserving a complete path for candidates that are
semantically compatible with the target snapshot.

Candidate generation and lowering should be interleaved so an invalid partial
spelling is rejected before its remaining cross-product is materialized.
Successful search must self-check the exact emitted Surface Click premise
against the replay context.

## Acceptance criteria

- There is no arbitrary fixed candidate-count cutoff.
- A valid late program-point spelling is found and its generated certificate
  replays.
- A no-spelling case fails within budget with a concise, specific diagnostic.
- Candidate work grows with semantically compatible snapshots rather than the
  unrestricted syntactic cross-product.
- Expansion and audit cover both the successful and exhausted cases.
- The default test suite passes without example or C-source reshaping.
