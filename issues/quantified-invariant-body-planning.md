# Finish explicit invariant-body planning

## Violated invariant

Automatic loop preservation must emit a complete checked proof of its exact
back-edge value and safety obligations. Expanded simple proofs must not
invoke the legacy invariant discovery ladder.

The kernel-owned `close_invariants by { ... }` scope already binds a completed
proof to its exact goal, snapshot, premises, and execution evidence. The gap is
constructing those proofs, not accepting a new kind of success token.

## Current green checkpoint

Entry/current snapshot presentation now lets copy3's explicit closure body
verify, expand, and independently recheck without legacy invariant discovery.
The regression is `explicit_invariant_body_copy3_checks_and_expands`.
It preserves the original C and converts only the already-expanded closer to
`close_invariants by { simp(); }`.

The recursive Surface structural planner's implication case is outlined into
a non-inlined helper. This keeps its large local temporaries off every nested
conjunction/quantifier frame without changing search order or stack limits.
The existing four-size, small-stack kernel reasoning regression remains enabled.

Bare closers and automatic preservation still use the legacy preparation
path. Do not describe this checkpoint as a completed loop migration.

## Remaining reproduction

`explicit_invariant_body_two_pass_sort_has_a_bounded_planning_miss`:

1. Verify the unchanged `mdtests/bubble_sort3_two_pass_sorted.md`.
2. Expand its grouped claim using the current green implementation.
3. Replace only bare closers with `close_invariants by { simp(); }`.
4. Require a local planning miss and zero legacy discovery during that
   explicit-body run. Never expand the failing explicit proof.

The fixed-range maximum invariant in the second loop is
`all_le_range(p, 0, 2, p[2])`. Its finite instances include
`p[0] <= p[2]` and `p[1] <= p[2]`. After the conditional swap, proving one
destination cell can require a different source cell's entry fact.

## Migration investigation (2026-09-08)

A task-worktree prototype made automatic preservation and bare closers emit
explicit bodies. Copy3 and bubble-pass verification, expansion, and rewritten
verification passed with zero legacy discovery. Most loop tests passed.
Countdown loops additionally needed a checked conversion from the existing
`0 <= n - 1` predecessor theorem to the written `n - 1 >= 0` goal.

The full gate stopped at the two-pass sorting expansion test:
1,273 tests passed before that failure. Its second-loop named maximum
invariants and the exact closure body reported local planning misses.

Further bounded experiments established that:

- The fixed-range entry universal can be instantiated explicitly at both
  constant indices. The loop index's singleton value can also be proved with
  existing integer theorems.
- Instantiating at symbolic store indices lets the existing certified-store
  rewrite change the source fact, but the compound inequality still does not
  reach the target through the checked transport route.
- Neither trying operand equalities separately nor supplying finite current
  cells as intermediate equality goals completed the proof.
- Broader candidate composition exhausted the existing 2,000,000-unit smart
  budget. No budget or stack limit was raised. That prototype is not a fix.

These experiments do not establish the precise missing primitive: distinguish
a planner omission from insufficient simple-step evidence before adding a
new rule. All automatic-migration and speculative transport changes were
reverted. No C, contract, or fixture expectations were weakened.

## Next implementation

1. Reduce the second-loop post-swap cell relation to a small proof test with
   its exact retained store equations, load origins, and snapshot bindings.
2. Identify a checkable, bounded composition from source instance through the
   stores to the destination cell. Prefer existing equality/transport steps;
   if execution must retain an additional value-flow witness, specify its
   exact inputs and rejection cases before changing the authority boundary.
3. Replace the expected miss with positive verification, expansion, and
   rewritten verification. Preserve the copy3 and bubble-pass regressions.
4. Re-enable automatic bodies only when the full gate passes; then delete
   `verify_lowered_invariant_path`, the legacy prefix probe, and legacy
   lowering-record builders. Preserve do-while paths with no continuing edge.

## Acceptance criteria

- Original copy3, bubble-pass, and sorting fixtures verify and expand to
  explicit closure bodies; expanded proofs recheck without legacy discovery.
- Missing value/safety children, wrong proof roots, stale snapshots, changed
  premises, and incomplete path evidence reject.
- Planning stays within existing limits. Simple checking remains
  output-sensitive, with deterministic scaling coverage.
- `scripts/check.sh` passes. Delete this issue and its index line together
  with the completed migration and updated documentation.
