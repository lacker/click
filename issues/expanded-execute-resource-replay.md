# Preserve folded resources across expanded execution replay

## Problem

The existing `expanded_read_step_keeps_named_range_separation_premises`
regression expands a successful `execute()` in `owned_string_pop`, then fails
when the emitted surface certificate is verified:

```text
execution proof for `owned_string_pop.contract` path 0 changed more than the
certified ghost resource representation
  missing certified resources: [owns owned_string(owner)]
  extra certified resources: [owns owner[0..4], owns owner->data[0..owner->cap]]
```

The search succeeds, but replay observes the unfolded representation where the
checked proof state expects the equivalent folded composite resource. This is
a certificate/tooling correctness failure, not an example-writing problem.

## Intended design

- Execution certificates must preserve the checked resource view at their
  boundary, even if search temporarily unfolds that resource to read a field.
- A folded composite and its explicitly unfolded body are not silently treated
  as identical kernel states. The certificate must contain the checked fold or
  unfold transition that relates them.
- Expansion and immediate replay must agree without depending on ambient proof
  steps that follow the selected tactic.

## Regression

Keep `expanded_read_step_keeps_named_range_separation_premises` as the focused
regression. Confirm that the generated certificate verifies both in isolation
and as part of the complete proof.

## Acceptance criteria

- Expanding the selected `execute()` succeeds and its emitted proof replays.
- Resource representation changes are explicit and kernel checked.
- A genuinely missing resource transition still produces the compact resource
  delta diagnostic.

