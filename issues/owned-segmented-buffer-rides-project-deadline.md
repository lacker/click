# Owned-segmented-buffer rides its project deadline under load

`examples/owned-segmented-buffer` verifies in about 22s warm debug CPU
against the default 30s project deadline. Under machine load it can cross
the deadline and fail, which makes the suite's green load-sensitive (observed
during 2026-08-11 reliability work, on pristine master, unrelated to the
changes then in flight).

Same shape as the binary-tree aggregate-cost issue: no individual tactic is
over budget (all are far inside the deterministic simple work budget), so the
cost lives in aggregate certification/verifier-core work.

## Acceptance criteria

- Warm ordinary verification completes with comfortable margin against the
  30s deadline (or the aggregate cost is attributed and reduced per the
  binary-tree/owned-string performance issues).
- No budget or deadline is raised, and no claim or C source is weakened.
