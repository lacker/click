# Attribute healthy proof volume to functions and claims

## Problem

`click profile` correctly distinguishes a slow tactic from a large amount of
healthy work. The completed owned-vector project is a useful pressure test: it
verified in roughly fifteen seconds, no individual operation crossed a class
threshold, and the report diagnosed `HEALTHY VOLUME`. That verdict is accurate
but not yet actionable. The report does not show which functions or claims own
most of the smart work, simple replay, certification, or verifier-core time.

The same run reported 116 unique smart source sites during audit and 122 smart
attempts during profiling. The difference is legitimate—one source occurrence
can execute on more than one proof path—but the tools make the user infer that
explanation.

## Invariant

When total verification cost is volume-bound, the profiler should identify the
largest semantic contributors without double-counting nested timing scopes or
pretending that a large healthy claim is a tactic bug.

## Design

- Attribute every exclusive SIMPLE, SMART, CONTROL, certification, and
  verifier-core event to its active function and claim when one exists.
- Keep frontend, environment, driver, and genuinely unowned work in their
  existing project-level buckets.
- Print a bounded `TOP FUNCTIONS / CLAIMS BY EXCLUSIVE TIME` section containing
  total exclusive time, bucket composition, and relevant work counts.
- Do not add claim-duration events on top of their child buckets. The per-claim
  rows must reconcile to the existing non-overlapping file totals.
- Report both unique smart source sites and dynamic smart attempts, with a
  one-line explanation when attempts exceed sites because of paths or repeated
  claim execution.
- Treat this as attribution, not a new failure threshold. Existing class and
  throughput diagnoses remain authoritative.

## Regression

Extend the synthetic profile-event tests with two claims whose nested tactic,
certification, and verifier-core events have known exclusive totals. Assert that
the per-claim totals sum to the file's attributable time exactly once and sort
in descending order.

Add a path-sensitive fixture with one smart source site executed twice and
assert that the report explicitly distinguishes one site from two attempts.

## Acceptance criteria

- A healthy-volume owned-vector profile names the functions and claims that
  account for most of its cost.
- Per-claim exclusive buckets reconcile with the existing file accounting;
  they never inflate wall time through nesting.
- Source-site and dynamic-attempt counts are both visible and explained.
- Output remains bounded to a small configurable top list.
- The profiler does not recommend expansion solely because a claim has high
  aggregate healthy volume.
