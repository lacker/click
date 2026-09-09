# Finish explicit invariant-body planning

## Violated invariant

Automatic loop preservation must emit a complete checked proof of its exact
back-edge value and safety obligations. Expanded simple proofs must not
invoke the legacy invariant discovery ladder.

The kernel-owned `close_invariants by { ... }` scope already binds a completed
proof to its exact goal, snapshot, premises, and execution evidence. The gap is
constructing those proofs, not accepting a new kind of success token.

## Current green checkpoint

Copy3 now also stores its expanded explicit closure proof in
`mdtests/copy3_array_demo.md`. The C and invariants are unchanged.

## Producer migration attempt (2026-09-09)

### Latest checkpoint and remaining blocker

Loop-preservation snapshot registration now records the loop's label aliases
as well as its numeric region. The regression
`loop_preservation_have_resolves_entry_label_and_expands` uses
`at(drain.entry, n)` inside a `have`, supplies an explicit closure body, and
verifies, expands, and rechecks without legacy discovery. The label-scope
failure listed in the historical census below is resolved.

A renewed staged migration reduced the nine remaining fixture failures to
four using existing tactics, with no C or invariant changes. Countdown,
lexicographic/nested countdown, loop-entry snapshot, and unchanged first-cell
preservation worked. The remaining cases were pointer/index equality,
branch-increment integer definedness, old-count closure, and quantified
permutation closure. The latter two roots require explicit implication and
quantifier handling; a root without a surface rendering is not evidence that
the kernel goal is absent.

The pointer attempt exposed a tooling failure rather than an ordinary bounded
miss: smart reasoning finds an equality but cannot emit its simple proof.
See [pointer-increment-equality-proof.md](pointer-increment-equality-proof.md)
for an executable reproduction independent of migration. Tooling-first policy
stops the migration here. The producer changes, temporary diagnostics, and
experimental fixture proofs were reverted; only the independently tested
label fix and focused regressions are retained. Bare/automatic closure and
the legacy builders/prefix probe remain. Fix the pointer proof gap before
resuming the remaining explicit fixture proofs and legacy deletion.

### Earlier prototype (historical)

The staged prototype migrated bare closers and automatic preparation to
completed bodies and removed the prefix probe. All 2,006 unit/CLI tests
passed after updating boundary-specific tests and supplying the existing
predecessor theorem plus `arithmetic() using { 0 <= n; }` in two countdown
proofs. The full fixture gate still rejected eleven fixtures:

- Bounded closure misses: `c_decreases_lexicographic_loop`, `c_decreases_loop`,
  `c_decreases_nested_loop`, `c_pointer_local_loop_invariant`,
  `fill_tail_keeps_first`, `loop_old_count_invariant`, `loop_preserve_branch`,
  and `loop_stdlib_permutation_invariant`.
- Stale evidence: `c_decreases_recursive_in_loop` and
  `c_decreases_resource_recursive_in_loop`. Investigate the remaining
  named-invariant prepass adding facts after an explicit body has closed;
  it must not invalidate or regenerate that exact body.
- `loop_entry_snapshot`: body planning reports unknown code region label
  `drain`; investigate label presentation in the nested body scope.

The proposed prepass guard was blocked by execution safety review. The
production prototype and temporary diagnostics were restored to the prior
checkpoint; only the independently checked saved copy3 proof is retained.
The migration is not complete. Resolve stale evidence and label scope first,
then supply explicit existing steps for bounded misses. Preserve negative
and stale-context coverage and do-while exits; never expand a failing proof.
No C, invariants, or limits were changed.

### Confirmed stale-context cause

The ordering fix is now implemented: the prepass checks for retained invariant
evidence, validates it against the exact bundle and execution context, and
does not add further named-invariant facts after that validation. A bare
close-request flag still does not authorize skipping proof construction.
Finalization retains its independent evidence validation. The regression
`completed_recursive_loop_bodies_skip_legacy_preplanning_and_recheck` verifies,
expands, and rechecks both recursive fixtures with explicit bodies and zero
legacy discovery; the combined isolated runtime is 0.54 seconds. Existing
wrong-root, incomplete-body, stale-snapshot, changed-premise, and changed-effect
rejection tests remain in force. Automatic/bare-closer migration and the
remaining fixture gaps are not included in this ordering fix.

A non-mutating probe reproduced the prepass on a cloned, already-closed
proof in both recursive-loop fixtures, replacing only the source bare closer
with an explicit `simp` body. Before the probe, exact bundle validation
succeeds. Joining the first named-invariant `have` adds one premise and
immediately produces `invariant closure has stale lowering evidence`.
Snapshot and effect-store identity both remain unchanged. The same happens
on both feasible branches and for the resource-recursive fixture. The
ordinary explicit runs pass (combined focused test: 0.237 seconds); probe
descendants are discarded and all diagnostic code was removed.

This confirms an ordering problem, not an invalid closure proof: the old
prepass mutates the premise store after the body has bound its exact context.
The migration should validate an existing completed body and bypass further
preplanning for it, or perform all preplanning before opening the body.
Do not treat a bare close-request flag as proof and do not relax stale-context
validation. The old legacy-prefix check happened to skip these redundant
`have`s; removing that check exposed the ordering mistake.

The unchanged two-pass sorting C now has a saved expanded proof in
`mdtests/bubble_sort3_two_pass_sorted.md`. All four invariant closers have
explicit bodies, with no remaining `simp` calls. The regression
`sorting_rewritten_invariant_body_checks_and_expands` verifies that saved
proof, expands/rechecks it, and asserts zero legacy discovery throughout.
Its isolated aggregate runtime is 0.86 seconds. The old search-heavy
construction and expected-miss tests were replaced by this positive check;
the reduced missing-transport rejection test remains.

This resolves the sorting example blocker without strengthening `simp`.
Automatic emission and legacy closer removal remain open. Investigation
sections below describe historical prototypes, not the current fixture.

Entry/current snapshot presentation now lets copy3's explicit closure body
verify, expand, and independently recheck without legacy invariant discovery.
The regression is `explicit_invariant_body_copy3_checks_and_expands`.
It preserves the original C and converts only the already-expanded closer to
`close_invariants by { simp(); }`.

The recursive Surface structural planner's connective cases are outlined into
non-inlined helpers. This keeps branch-local temporaries out of the shared
dispatcher without changing search order or stack limits. Snapshot annotation
uses an explicit postorder work stack, with one nonrecursive node-construction
helper. Small-stack regressions cover its supported depth, depth rejection,
operand order, and linear work over multiple input sizes.
The existing four-size, small-stack kernel reasoning regression remains enabled.

Bare closers and automatic preservation still use the legacy preparation
path. Do not describe this checkpoint as a completed loop migration.

## Historical unassisted reproduction

The former `explicit_invariant_body_two_pass_sort_has_a_bounded_planning_miss`
test used the pre-expansion fixture:

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

1. Use explicit branch proofs where smart planning misses; stronger `simp`
   is not a prerequisite for migration. A full sorting prototype supplied
   both branch arguments with existing tactics (see below); reduce its
   regression runtime before landing it.
2. Preserve positive verification, expansion, and rewritten verification
   of explicit bodies, including copy3 and bubble-pass.
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

The full reproduction now explicitly enumerates the fixed-range invariant and
carries the branch ordering through the swap. Its growing invariant's
`unfold; rewrite(j == 1); simp` body constructs a checked proof, expands, and
independently rechecks. The regression is
`sorting_rewritten_invariant_body_checks_and_expands`; it retains the original
C and invariants and leaves the original legacy closers in place for this
positive proof-body check.

The rewrite retains typed load-equality witnesses, including an exact stored
source value, the selected destination-address equality, and intervening
memory edges. This connects the rewritten source goal to its kernel value
representation. The mid-execution `have` success-without-a-proof fallback is
deleted: success now requires a retained body. Atomic derivation payloads are
boxed to keep unrelated evidence off recursive frames; the small-stack
scaling regression and a compact representation-size assertion cover this.

The same test separately replaces all bare closers with explicit `simp`
bodies and requires a bounded closure-planning miss with zero legacy discovery.
That failing variant is not expanded. Exact closure value/safety planning,
automatic body emission, and legacy closer removal remain open.

The aggregate regression also crosses nextest's 10-second slow-test threshold:
an isolated run on `8ccc9bd6` took 11.5 seconds, and a resource-match worktree
run took 11.9 seconds. This is existing test-level slowness, not a resource-match
regression. Keep the unchanged-C budget-exhaustion reproduction, but reduce
or separate its setup/verification work so the regression itself is prompt;
do not raise the tactic or test limits or expand the failing proof.

## Exact closure census (2026-09-08, d25256e6)

Temporary diagnostics on the explicit-body variant of
`sorting_rewritten_invariant_body_checks_and_expands` first attempted the
complete closure body, then split the actual failing root into checked child
scopes. Each child was tested separately with ordinary `simp`, introducing
its outer implication premises first. The diagnostics were removed afterward;
neither the C nor the proof fixture was changed.

The augmented swap arm closes successfully. The subsequent no-swap arm in
the second loop has eight children:

| Obligation | Individual planning result |
| --- | --- |
| `j >= 0`, `j <= 1` | Both prove |
| Fixed-range index and endpoint load safety | Both prove |
| Fixed-range maximum value invariant | Proves |
| Growing-range index and endpoint load safety | Both prove |
| Growing-range maximum value invariant | Bounded miss |

The remaining value goal is
`forall (k: int32) { 0 <= k and 0 <= k and k < j implies p[k] <= p[j] }`.
It still misses after introducing all six outer implication premises,
returning `None` after 48,724 measured work units, not a budget error.
Thus this reproduction is not blocked on load safety or merely conjunction
assembly. At this edge the index has advanced from zero to one, and the
no-swap condition supplies the ordering needed for the singleton range.

The next bounded investigation should isolate composition of that branch
ordering, the index update, and finite-range quantifier planning in the exact
checked scope. The census does not yet establish whether a simple-step
evidence gap exists. Do not add a new proof rule or broaden search based only
on this miss. These results concern the augmented regression, not a claim
that unassisted automatic preservation now handles the original fixture.

## Explicit no-swap proof follow-up

An uncommitted prototype resolved the census miss in
`sorting_rewritten_invariant_body_checks_and_expands` by spelling out the
no-swap argument, without changing C, invariants, or `simp`:

1. Prove current `j == 1` with local `simp`.
2. Transport `at(before_swap, not (p[j + 1] < p[j]))` to
   `not (p[1] < p[0])`, explicitly supplying the entry `j == 0` fact.
3. Apply `int32_not_lt_implies_ge(p[1], p[0])`, then use local `simp`
   to finish the goal spelled `p[0] <= p[1]`.
4. Unfold the growing invariant, rewrite `j == 1`, and `enumerate()`.

The prototype passed explicit closure verification, expansion, and
expanded-proof rechecking, with zero legacy discovery across those runs.
However, the aggregate test took 22.75 seconds even after removing redundant
augmented legacy-closure verification/expansion. Per tooling-stability policy,
the test edits were reverted to the existing checkpoint; the committed test
still expects the original bounded miss. The next task is to isolate timing
of setup, verification, expansion, and rechecking, then reduce or separate
the regression work without raising limits or removing expansion coverage.
The successful explicit argument establishes that strengthening `simp` or
adding a proof rule is not necessary for this no-swap obligation.

### Stage timing follow-up

The 22.75-second result was the aggregate test, not one verification.
Temporary stage timers (wall and thread CPU) reproduced the successful
prototype. A concurrent test suite in another worktree caused visible
contention in the first measurement. A quieter repeat, without the optional
deterministic-work counter, measured:

| Stage | Wall seconds | Thread CPU seconds |
| --- | ---: | ---: |
| Original verification | 0.739 | 0.737 |
| Original expansion/setup | 0.727 | 0.725 |
| Explicit-body verification | 11.823 | 11.791 |
| Explicit-body expansion | 13.123 | 13.023 |
| Expanded proof rechecking | 0.400 | 0.399 |

All stages passed, with zero legacy discovery across the explicit stages.
Contention affects wall time but does not explain the expensive explicit
planning: the quieter run consumed nearly the same wall and CPU time.
Expanded simple-proof checking is much cheaper. Next isolate the retained
smart-tactic planning sites, not the final expanded proof checker. These
are unoptimized test-build measurements; no release timing claim is implied.
Temporary timing and prototype changes were removed afterward.

### Planning-site attribution and duplicate-query cleanup

Structured profiling of the successful explicit prototype attributes the
large costs to the closure bodies, not the newly added no-swap argument.
Second-loop `close_invariants` at statement 17/source 45 (swap) took about
3–4 seconds per execution, and source 54 (no swap) about 1.4 seconds.
Both sites execute twice during verification. The enclosing loop events
are inclusive, not additional costs. First-loop closers cost about 0.2–0.4
seconds each. Atomic attempts include unsuccessful reasoning on conjunctions
and quantified load-safety obligations before structural decomposition.

One avoidable operation was found: after an atomic candidate declined,
`try_simp_closure_after_direct_with_surfaces_and_function_unfold` repeated
`selected_simp_derivation_with_surfaces` solely to recover its premises.
It now retains those premises from the first query, without changing search
order or proof rules. The same prototype still verifies; deterministic work
for the two swap executions fell from 610,389/372,083 to 577,752/339,446,
and for no-swap from 163,864/155,300 to 146,824/138,260. First-loop closure
work dropped about 27–32%. This is a modest constant-factor cleanup, not a
claim that smart planning is now cheap or asymptotically improved.

The explicit prototype and profiling diagnostics were removed afterward.
Expanded simple checking remains the important performance boundary; do not
broaden `simp` search merely to automate the explicit branch argument.

## Acceptance criteria

- Original copy3, bubble-pass, and sorting fixtures verify and expand to
  explicit closure bodies; expanded proofs recheck without legacy discovery.
- Missing value/safety children, wrong proof roots, stale snapshots, changed
  premises, and incomplete path evidence reject.
- Planning stays within existing limits. Simple checking remains
  output-sensitive, with deterministic scaling coverage.
- The explicit sorting transport regression stays below the slow-test
  threshold while retaining its local failure and stack-safety checks.
- `scripts/check.sh` passes. Delete this issue and its index line together
  with the completed migration and updated documentation.
