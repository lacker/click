# Binary-tree verification has excessive aggregate verifier-core cost

The unchanged `examples/binary-tree` project verifies successfully but takes
roughly 11 seconds of CPU time in a warm debug CLI run. This is too slow for
the intended interactive workflow even though no individual tactic is slow.

```sh
target/debug/click verify examples/binary-tree
target/debug/click profile examples/binary-tree
```

A representative profile attributed about 1.6 seconds to simple tactics, 1.3
seconds to smart tactics, 1.7 seconds to certification, and 6.3 seconds to
verifier core work. The largest functions were `tree_rotate_left` (about 4.3
seconds), `tree_sum_root_and_children` (about 3.0 seconds), and `tree_walk`
(about 2.4 seconds). Timing diagnostics place most of the unattributed cost
after the visible tactics, in ordered-proof finishing and kernel
memory/resource reasoning.

The outer Rust test threshold is an aggregate harness guard, not a per-project
semantic budget. Direct CLI and already-built harness timings agree, so this
is not a test-harness-only slowdown. The problem is the project's real
aggregate verification cost.

## Regression design

Add sufficiently narrow profiling around ordered-proof finishing to separate
independent kernel certification, replayed/certified outcome pairing, and
resource-representation checks. Preserve the existing C and Click proof as
the regression. Optimize only after repeated work or an avoidable algorithmic
cost is identified; do not change search heuristics merely because the
aggregate project is slow.

## Acceptance criteria

- The unchanged binary-tree project verifies within a few seconds in the
  normal direct-CLI development workflow.
- Profiles attribute ordered-proof finishing cost to actionable named phases
  rather than a broad `verifier core` bucket.
- No tactic, project, or test budget is raised.
- No C source, claim, or example structure is weakened or reshaped.
- Any optimization has a focused deterministic-work or cache-behavior
  regression where practical.
