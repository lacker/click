# `execute` expansion drops a certified post-call fact

## Problem

Whole-function `execute()` can verify a chain of opaque calls but emit a
certificate that fails replay because a fact certified by one call is not
selected as a premise for the next call.

The `refcount_pipeline` reproduction is:

1. initialize a counted population at one;
2. retain it to two;
3. release it back to one; and
4. call a final-release function requiring the stored count to equal one.

The verified nonfinal release publishes the post-population fact against its
new call-havoc snapshot. Search uses that fact successfully. Expansion then
emits the final `step() using {}` without it, and replay reports that the final
release precondition cannot be reconstructed from the older entry snapshots.
The explicit proof in `examples/refcount/refcount.click` is green by naming the
post-release fact before the final call.

This is a tooling reliability bug, not a request to broaden heuristic search:
the smart tactic already succeeded, so its selected proof must be expandable.

## Regression

Add a focused mdtest with three opaque calls whose certified memory
postcondition at call 2 is the exact precondition of call 3. The whole caller
must verify with `execute()`, and its generated surface certificate must replay
without replacing the C or adding a redundant explicit postcondition.

## Acceptance criteria

- Search records or reconstructs the certified post-call premise it actually
  used.
- Expansion includes that premise in the following `step() using` block.
- The result remains bounded; do not expand condition-premise search beyond
  its documented small heuristic merely to make this case pass.
- The explicit simple proof remains valid.
