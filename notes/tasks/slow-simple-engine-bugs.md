# Slow simple tactics — engine bugs (plan.md rule 5)

Status: open
Claimed:

A slow SIMPLE tactic is an error in Click. `click-profile` (2026-07-31
coverage work) measured two, both far over the 500 ms simple budget.
Fixing the first is also what de-quarantines `bubble_sort3`
(passes at 137 s against the 30 s mdtest limit — a quarantine-for-cost
entry, i.e. a burn-down obligation per conventions.md).

## Bug 1: the invariant-closer replay (65 s, 130x over budget)

`c_loop_invariants_hold_at_back_edge_using` — the *replay* half of loop
verification, run by the caller after `close_invariants` sets its flag —
takes 65 s of `bubble_sort3_two_pass_sorted`'s 137 s. Its cost profile
(counted with call-site probes on the smaller `bubble_pass3`, sampled on
`bubble_sort3`; full data was in the named-memory-states arc log,
2026-07-31 session 4):

- `bitvector_terms_proven_equal_for_memory_resolution` entered 564 888
  times, ~7 of 9 s on bubble_pass3; **95% of calls return false** — the
  cost is a failing search over the fact set
  (`bitvector_terms_equal_from_facts`, `exact_condition_value` twice per
  call via the `[1, 4]` byte-width arm), not snapshot comparison.
- Only 6 of 540 k top-level comparisons are load-vs-load, so memory-DAG
  arms cannot reach this cost (measured; see the arc file's dead ends).
- The final-index split is not where the time is (depth-2 experiment:
  +20 s, no outcome change).

**Lead worth trying first:** the replay re-derives exactly what the
smart planner derived one call earlier — the two halves of the run are
the same derivation twice. Caching/reusing the planner's result for the
replay may beat optimizing the derivation itself.

## Bug 2: a 29 s `fold` (58x over budget)

`fold` in `field_derived_precise_effect_after_metadata_write` takes
28.9 s — an independent path from bug 1 (field_derived is otherwise 86%
smart-failure time).

## Small related follow-up

Auto-planned loop-phase certificates should report source indices the
surface proof actually has, so their steps get locations in profiles.

## Repro

```
cargo run --quiet --bin click-profile -- --time-limit 10m --threshold 500ms \
  mdtests/bubble_sort3_two_pass_sorted.md
cargo run --quiet --bin click-profile -- --time-limit 10m --threshold 500ms \
  mdtests/field_derived_precise_effect_after_metadata_write.md
```

Done when: no SIMPLE entry over 500 ms in either profile, and
`bubble_sort3_two_pass_sorted.md` passes inside the 30 s mdtest limit
and de-quarantines.
