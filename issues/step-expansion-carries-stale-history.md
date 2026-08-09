# Keep stale proof history out of step certificates

A smart opaque-call step succeeded during bounded-pool verification, but its
generated `step() using` certificate listed dozens of facts from earlier
statement snapshots. Replay then exceeded the simple-tactic budget.

Historical facts may remain available for later pure reasoning, but a step
certificate should contain only the prerequisites actually needed by that
transition. `consults_conditions` is currently too coarse if it causes every
ambient condition from the proof history to be emitted.

## Regression

Use a short caller that performs several writes and opaque calls, retaining
facts at each program point, before one final call with two or three current
preconditions. Expand that final smart step.

## Acceptance criteria

- The expanded step contains current prerequisites, not unrelated historical
  snapshots.
- The emitted certificate replays within the simple-tactic budget.
- Conditions genuinely used for overflow, bounds, or memory access are not
  dropped.
- A failed minimization produces a concise diagnostic rather than the entire
  internal state.
