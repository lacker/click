# `condition_polarity_equivalent` treats "no canonical form" as a match

Status: open — diagnosed, fix known, blocked on three examples that depend
on the buggy behaviour
Claimed: claude/nervous-ptolemy-90e738 (worktree agent-a156f211eec3701d6), 2026-07-30

Found while fixing the certificate premise policy
(`lib-ignored-expansion-tests.md`, 2026-07-30). Not fixed there: the
premise work does not need it, and fixing it takes three example
projects red.

## The bug

`src/lang/click/proof.rs`, `condition_polarity_equivalent`:

```rust
(Proposition::ConditionIs(lc, lv), Proposition::ConditionIs(rc, rv)) => {
    canonical_order_condition(lc, *lv) == canonical_order_condition(rc, *rv)
}
```

`canonical_order_condition` returns `Option<(Bitvector32Term, Bitvector32Term, bool)>`
and only comparisons have a canonical order form. Everything else — an
overflow check, `PointerOffsetEqual`, `Bitvector32Equal`, a constant —
returns `None`. So **any two conditions that both lack a canonical form
compare equal**.

`condition_polarity_equivalent` backs `exact_fact_contains_conjunct`,
hence `exact_fact_is_available`, which is the availability predicate for
`step using` / `transport using` premises, for statement prerequisites,
and for the certified-transition selection. The predicate therefore
answers "yes, that fact is available" for a non-comparison condition
whenever the available set holds *any other* non-comparison condition.

Observed concretely: in `verifies_loop_invariants_and_statement_assert`
the ambient set holds `ConditionIs(Constant(true), true)`, which made
`ConditionIs(Bitvector32SignedAddOverflows(i, 1), false)` register as
exactly available.

## The fix, and why it is blocked

Requiring a form on both sides is clearly the right predicate:

```rust
matches!(
    (canonical_order_condition(lc, *lv), canonical_order_condition(rc, *rv)),
    (Some(left), Some(right)) if left == right
)
```

`cargo nextest run --lib --bins` and `cargo test --test mdtests` stay
green with it. `cargo test --test examples` goes to **3 of 4 failed**:

- `examples/input-cursor` — `input_cursor_shared_pipeline.contract`
  tactic 17: `` `transport using` requires an exact premise ``, missing
  `ConditionIs(PointerOffsetEqual(..))`
- `examples/owned-segmented-buffer` — `owned_segmented_buffer_pipeline.contract`
  tactic 12: `` `transport using` requires a source derivable from its
  explicit facts ``, missing `ConditionIs(Bitvector32Equal(..))`
- `examples/owned-split-buffer` — same shape

In each the required fact and an available fact print alike and differ
only by memory snapshot. The accidental `None == None` equivalence is
standing in for snapshot-insensitive matching that those pipelines need.

## What a real fix has to do

Give the non-comparison conditions a genuine equivalence instead of an
accidental one — most likely routing them through the same
materialization/snapshot normalisation that
`materialization_equivalent_available_fact` and
`normalize_direct_atomic_memory_loads` already provide for the memory
facts — and only then tighten `condition_polarity_equivalent`.

Repro for the blocked direction: apply the `matches!` form above and run
`cargo test --test examples`.
