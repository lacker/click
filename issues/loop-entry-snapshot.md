# Keep loop-entry snapshots stable during preservation

**Severity: critical.** A loop preservation proof must not be able to prove a
claim using the arbitrary havocked loop-head state and export it as a claim
about the real state just before the loop.

**Violated invariant.** A program-point selector has one meaning at every use.
`at(loop_label.entry, expression)` denotes the state immediately before the
labeled loop begins, including inside its `preserve` proof.

**Root cause.** Loop preservation creates a fresh abstract loop-head state for
induction. The preservation context accidentally stored that state as its
`loop_entry_state`, and the surface proof driver recorded it for the loop-entry
snapshot. This allowed an invariant to be checked against a different state
than the one used by later post-loop reasoning.

**Regression.** `mdtests/loop_entry_snapshot_rejected.md` proves `x - 1 <=
at(L.entry, x)` as an invariant while incrementing `x` from zero to `n`. The
claim is false for `n >= 5`, but was accepted when `at(L.entry, x)` resolved to
the havocked loop head.

**Acceptance criteria.**

- The regression is rejected because `x - 1 <= at(L.entry, x)` is not
  preserved.
- `at(loop_label.entry, ...)` always uses the pre-loop state, including inside
  `preserve`; the current arbitrary loop-head state remains available through
  ordinary unwrapped expressions.
- A positive loop-entry snapshot test continues to pass and demonstrates a
  valid invariant relating the current value to the pre-loop value.
- The `at(...)` reference documentation describes this behavior.
