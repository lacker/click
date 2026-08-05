# Make smart-search success imply certificate replay

## Problem

While verifying owned-vector growth, smart `execute()` search found an outcome
and generated a surface certificate, but replay of that generated certificate
failed. Other runs reached final contract certification before reporting that
the searched execution and certified ghost-resource representation differed.

Search success without replay is a serious invariant violation. The verifier
must never accept “search succeeded” as a useful intermediate result when its
certificate is not accepted by the deterministic checker.

## Required invariant

A smart tactic has only two successful outcomes:

1. it returns a certificate that has already replayed successfully against the
   exact pre-state and selected goal; or
2. it returns an internal checked object whose serialization is separately
   tested to replay to the same checked result.

All other outcomes are tactic failure. They must identify whether search,
surface lowering, or replay disagreed; callers must not continue into later
proof steps with the searched state.

Fresh symbolic identities require special care. Search and replay must either
share a stable allocation-identity scheme or compare alpha-equivalent checked
states. Ad hoc numeric equality of fresh IDs is not a sound certificate
boundary.

## Regression

Use a small function with a fallible runtime allocation, an opaque helper call,
and two proof branches. Reproduce both observed failure classes:

- generated `execute()` surface proof fails immediately on replay; and
- search state and replay state differ only in ghost resources or fresh names.

Also retain `mdtests/c_null_pointer_conversion.md` as a focused non-allocation
reproducer: `call_with_null()` currently reports that `execute` used an
assumption-derived theorem premise without a replayable derivation while
applying `pointer_is_null(0)`. This shows the invariant is broader than fresh
heap identity.

The regression should exercise the smart-tactic API directly and through
`click-expand`.

## Acceptance criteria

- No API reports smart success before deterministic replay succeeds.
- Failed replay leaves the proof state unchanged and produces a compact error.
- Fresh identifiers are compared or generated according to a documented stable
  rule.
- Unit tests deliberately perturb a certificate and prove that it cannot be
  mistaken for search success.
- `click audit` exercises this invariant for every expanded smart site.
