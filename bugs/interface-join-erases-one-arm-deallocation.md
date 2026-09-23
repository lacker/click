# The interface join erases a deallocation one arm performed

P1. A continuation after a conditional must reject an alias of an object
whose lifetime any incoming arm has ended; a status join must not erase an
arm's record.

## What was found

`with_interface_memory_havoc_preserving_loans`
(`src/kernel/primitives/memory_state.rs:2212`) **unions** `live_allocations`
across arms (with a size-agreement error) but **intersects**
`deallocated_allocations` (line 2225: `{!live_allocations.contains_key(base)}`
and all-arms-agree), while the state doc at the same file claims the
tombstones are *unioned* so that "a continuation must reject an alias if
any incoming arm has ended its automatic lifetime" (`memory_state.rs:2143`).
The combination is exactly the unsafe one: arm A frees allocation P (its
state: `live={} , deallocated={P}`), arm B keeps it live (`live={P}`), and
the join exports `live={P} , deallocated={}` — the possibly-freed status is
erased, the unioned-live arm wins, and `is_deallocated_heap_address` answers
false while `is_live_heap_address` answers true at the join.

Machine-confirmed:
`hunt_investigation_interface_join_erases_one_arm_deallocation`
(`src/kernel/primitives/memory_state.rs` investigation module) — after the
join, `is_deallocated_heap_address(base)` answers false and the joined
state claims the possibly-freed allocation is live.

Alias path: a load through an alias spelling of the allocation at the
joined state resolves through the *live* record — the join lost the arm
that owns "this object may be deallocated here", so every subsequent
accept/refusal decision that trusts the join to be a *valid* union of arm
knowledge is wrong for the freeing arm's facts.

## Intended regression

The investigation test converted to a true regression: for every base
recorded deallocated by any incoming arm, the joined state must either
remain deallocated (tombstone union) or drop the live record until the
arm disagrees as an explicit hypothesis — no arm's deallocation may be
erased by the join, and the joined queries must answer per the union.

## Acceptance

- [ ] The join preserves every arm's deallocation record (or drops the live
      record for bases that some arm freed), so an alias of a
      freed-on-one-arm allocation does not read as live at the join, with
      the regression green.
- [ ] `scripts/check.sh` green.
