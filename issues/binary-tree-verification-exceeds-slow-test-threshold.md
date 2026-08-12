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

Update (2026-08-11): the `step` at `tree_sum_root_and_children` statement 2
(source tactic 5, the bounded three-way sum) sits at the 500ms simple
wall-clock budget and now blocks verification outright under ordinary machine
load. On an idle machine it measures about 390ms and the project verifies; on
the same machine under concurrent load it crosses the budget on every run and
`click verify examples/binary-tree` fails with "a slow simple tactic is a
Click engine bug". A build of the pre-`e9460ff` tree shows the same crossing,
so this is long-standing cost, not a recent regression; it was masked while
the project also failed earlier at `tree_is_leaf` (since fixed). The project
is quarantined in `tests/examples.rs` against this issue until the step's
verifier path is reduced. This is the same machine-speed-dependent
enforcement problem that was tracked in
`input-cursor-simple-step-crosses-budget.md` (closed 2026-08-12 by the
deterministic work budgets).
Full-project wall time also varied between passing runs (one 3.9s outlier
against a 14-19s norm on identical input), which suggests run-to-run variance
in derivation memo hits worth capturing while profiling.

Update (2026-08-12): the repeated work suspected above is confirmed and
partially fixed. Every order-path query re-collected `condition_order_facts`
from an unchanged fact set, and the same top-level pointer/bitvector
memory-resolution queries were re-run dozens of times per step from
separation and resource-context scans; both are now memoized by fact-set
content identity with the decide-memo truncation discipline and kernel
cache-behavior regressions. The hot step's deterministic cost fell from
63,752 to 40,460 work units. Simple-tactic budgets are now enforced
primarily in deterministic work units (100,000 simple) with the wall clock
demoted to a generous backstop, so the step-level machine-load-dependent
failure mode above is gone: every binary-tree tactic is now well inside its
deterministic budget (worst simple tactic 40,460 of 100,000 units).

The project nonetheless stays quarantined for its original aggregate cost.
On the merged whole-claim-gate base the full project measures about 25
seconds of warm debug CPU, riding the default 30-second project deadline: a
moderately loaded machine pushes the wall time over the limit and the run
fails (currently with the misleading diff tracked in
[deadline-truncation-masquerades-as-ghost-region-mismatch.md](deadline-truncation-masquerades-as-ghost-region-mismatch.md)).
`click verify --time-limit 3m examples/binary-tree` verifies cleanly, with
budgets enforced, on the same tree. Un-quarantine when the aggregate cost
fits the default deadline with real margin; that requires the ordered-proof
finishing and certification attribution work below, not budget changes.

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
