# Expand or reduce the slow owned-string pop step

## Problem

`owned_string_pop_preserves_first.contract` has a successful SMART `step` at
statement 2 taking about 2.3 seconds exclusive, above the two-second smart
budget.

## Work

Run `click-expand` on the exact reported site. The emitted simple certificate
must parse, replay, verify cold, and reach an audit fixed point. If expansion
fails or replay differs, stop and fix the corresponding tooling issue rather
than hand-writing an approximation. If the expanded simple step is itself slow,
reduce the engine path instead.

## Acceptance criteria

- The source contains a readable replay certificate or the smart search is
  reduced below budget.
- Expansion and audit pass on the site.
- No replacement simple tactic crosses 500ms.
- Owned-string can leave quarantine once its control-proof issue also passes.
