# Isolate `click-expand` to the selected proof unit

## Problem

Expanding the slow `vector_push` arithmetic site failed because an unrelated
`vector_grow` proof elsewhere in the same sidecar had a branched frame
certificate mismatch. After growth was removed, expansion of the unchanged push
site succeeded.

Selecting one source location should not require unrelated proof units to search
or replay successfully. Otherwise a broken experimental function prevents users
from expanding and repairing independent code, and targeted expansion does not
match targeted verification semantics.

## Intended design

- Parse and typecheck the complete sidecar as needed for declarations and
  dependencies.
- Verify only the selected proof unit and the transitive contracts it calls.
- Preserve all unselected source text exactly in the emitted file.
- Do not execute, search, lower certificates for, or certify unrelated proof
  units.
- If a required dependency is broken, report the dependency path that made it
  relevant.

This is separate from path alignment inside the selected proof; that remains in
`branched-expansion-path-alignment.md`.

## Regression

Create one sidecar with a valid expandable function and a second independent
function whose proof intentionally fails. Expanding the valid location must
emit a changed parseable sidecar. Targeted verification of the rewritten unit
must pass even though whole-file verification still reports the unrelated
failure.

Add a companion where the failing function is a called dependency and confirm
that expansion fails with the dependency chain.

## Acceptance criteria

- Unrelated broken proofs do not block expansion.
- Required broken dependencies do block expansion with a focused diagnostic.
- Output outside the selected proof unit is byte-for-byte unchanged.
- Targeted expand/verify semantics agree and audit retains its whole-inventory
  guarantees.
