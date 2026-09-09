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

1. Generalize the existing-step composition demonstrated below to the full
   quantified invariant context. Do not start by adding a value-flow witness:
   the reduced loop already verifies and expands with existing transport.
2. Replace the expected miss with positive verification, expansion, and
   rewritten verification. Preserve the copy3 and bubble-pass regressions.
3. Re-enable automatic bodies only when the full gate passes; then delete
   `verify_lowered_invariant_path`, the legacy prefix probe, and legacy
   lowering-record builders. Preserve do-while paths with no continuing edge.

## Swap reduction follow-up (2026-09-08)

The new `explicit_straight_line_swap_transports_an_entry_bound` test confirms
that existing explicit transport moves an old source cell's inequality to
its new destination, for both a literal index and a symbolic index with an
exact equality premise.

`explicit_swap_loop_transports_both_entry_bounds_and_expands` isolates the
second sorting loop, with the two ordinary invariants `p[0] <= p[2]` and
`p[1] <= p[2]`. Its unchanged symbolic-index swap verifies, expands, and
independently rechecks with zero legacy invariant discovery:

1. Before execution, prove `j == 0` using
   `int32_lt_successor_implies_le` and `int32_le_and_not_lt_implies_eq`.
2. Mark that entry snapshot.
3. Execute the swap and index increment with ordinary `step()`.
4. Explicitly transport the old `p[1] <= p[2]` fact to current
   `p[0] <= p[2]`, and the old `p[0] <= p[2]` fact to current
   `p[1] <= p[2]`, listing the source and entry index equality.
5. Finish with `close_invariants by { simp(); }`.

Removing the two transports returns the original bounded closure miss.
Thus the first failure does not require quantifiers, and existing simple
steps are sufficient for the reduced value movement. Asking smart `have`
proofs to rediscover the separate cell equalities was less successful; that
is not evidence that a new equality primitive is required.

The full unchanged two-pass fixture was then tested with analogous explicit
index proof, two finite entry instances, and transports. This exposed oversized
recursive frames in both proposition lowering and source synthesis. Their
leaf/binder work is now outlined without changing proof rules, traversal
order, synthesis depth/work limits, or the ordinary stack size. Four-size
1 MiB-stack regressions check linear visits/work in both directions.

The initial full reproduction returned a local smart-work-budget failure
from `close_invariants`, not a stack overflow. Further explicit steps now
enumerate the fixed-range invariant and carry the branch ordering through the
swap. The growing invariant's `unfold; rewrite(j == 1); simp` body exposes a
more specific proof-body conversion failure. The regression is now named
`explicit_sorting_rewritten_invariant_reports_body_failure`; see
[the focused tooling issue](rewritten-invariant-proof-body.md). Fix that
boundary before resuming automatic migration. The failing proof is not
expanded, and the reduced C is not substituted for the original fixture.

## Acceptance criteria

- Original copy3, bubble-pass, and sorting fixtures verify and expand to
  explicit closure bodies; expanded proofs recheck without legacy discovery.
- Missing value/safety children, wrong proof roots, stale snapshots, changed
  premises, and incomplete path evidence reject.
- Planning stays within existing limits. Simple checking remains
  output-sensitive, with deterministic scaling coverage.
- `scripts/check.sh` passes. Delete this issue and its index line together
  with the completed migration and updated documentation.
