# Expansion replay recursion exhausts the stack on ordinary edits

## Violated invariant

Adding a local variable to a verifier function must not break an unrelated
test. Today it does: several functions on the expansion-replay path sit in
a recursion deep enough that a few hundred extra bytes per frame overflow
the stack, and the failure surfaces as a `SIGABRT` in a test whose name
gives no hint of the edit.

The canary is `lang::click::tests::expansion_tests::selected_pure_case_split_simp_expands_by_removal`,
which aborts with `has overflowed its stack` rather than failing an
assertion. Stack overflow produces no backtrace, so the edit that caused
it is not visible from the failure; it has to be bisected by reverting
changes one at a time.

Three separate edits triggered it while landing the load-canonicalization
work (2026-08-19), none of them algorithmic:

- two ordinary locals plus a closure added to `check_step_using_facts`
  (`src/lang/click/proof/replay_engine/statement_step.rs`);
- an enum variant carrying two inline four-field tuples added to
  `SnapshotBlindPropositionKey` (`src/lang/click/proof/fact_reasoning.rs`),
  fixed by boxing the payload;
- a single `let conclusion: Proposition` shared across match arms in
  `prove_c_condition_fact_transport_with_assumptions`
  (`src/kernel/memory_provenance.rs`), fixed by returning per arm so the
  by-value `Proposition` never lives in the recursive frame.

Each was worked around by moving the work behind an `#[inline(never)]`
adapter, boxing, or restructuring to avoid a large by-value local. The
tree now carries 28 `#[inline(never)]` attributes, a growing number of
which exist only to keep frames small. That is a workaround for unbounded
recursion depth, not a fix, and it silently taxes every future edit to
these files.

The fixture harnesses already compensate: both `tests/mdtests.rs` and
`tests/examples.rs` spawn their verifier threads with
`.stack_size(64 * 1024 * 1024)`. The unit-test path has no such override,
which is why the canary is a lib test rather than a fixture. Raising the
lib tests to a 64 MB stack would hide the symptom while leaving the depth
unbounded, and would diverge the two paths further.

## What to find out first

The depth is not currently known. Instrument the replay/expansion entry
points with a depth counter (or run the canary under a debugger and count
frames) and record: the maximum recursion depth reached, which cycle
carries it, and the per-frame size of the largest offenders. Without that
number, any bound chosen is arbitrary.

## Intended regression

- A deterministic test that runs the canary's expansion on a thread with a
  *small* explicit stack (well under the current default) and passes,
  demonstrating the recursion fits a stated budget.
- A depth assertion or bounded-depth guard on the replay recursion that
  fails loudly with an actionable message if the budget is exceeded,
  instead of aborting the process.

## Acceptance criteria

- The recursion's maximum depth over both fixture gates is measured and
  recorded here.
- Expansion replay runs within a documented stack budget, enforced by the
  regression above, so an added local cannot abort an unrelated test.
- The `#[inline(never)]` attributes that exist only to shrink frames are
  removed, or each remaining one states why the frame must stay small
  beyond "the stack overflows otherwise".
- This file and its Open-list line are deleted when the fix, its
  regression coverage, and any documentation land.
