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

## Status 2026-08-12

Whole-project measurement is currently blocked: the project is quarantined
for the independent
[grouped-simp expressibility failure](binary-tree-grouped-simp-transition-not-expressible.md),
which fails `tree_is_leaf.contract` before the expensive functions run. The
`tree_sum_root_and_children` proof unit still verifies through the targeted
entry point (`click verify examples/binary-tree/binary_tree.click:153:5`)
and was used as the reduction workload.

Attribution of its hot `step` (statement 2, source tactic 5) confirmed the
suspected repeated work in kernel memory/resource reasoning: every
order-path query re-collected `condition_order_facts` from an unchanged fact
set, and the same top-level pointer/bitvector memory-resolution queries were
re-run dozens of times per step from separation and resource-context scans.
Both are now memoized by fact-set content identity with the decide-memo
truncation discipline, with kernel cache-behavior regressions. The step's
deterministic cost fell from 63,752 to 40,460 work units; input-cursor's
analogous step fell from 92,826 to 35,368.

Tactic budgets are now enforced primarily in deterministic work units
(simple 100,000), so the pass/fail behavior of this project no longer
depends on machine speed; the remaining problem is aggregate latency only.
Re-profile the whole project once the grouped-simp quarantine lifts.

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
