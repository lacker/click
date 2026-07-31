# Invariant-closer replay: 65 s SIMPLE, 130x over budget

Status: open
Claimed:

`c_loop_invariants_hold_at_back_edge_using` — the replay half of loop
verification — takes 65 s of `bubble_sort3_two_pass_sorted`'s 137 s
pass. A slow SIMPLE tactic is an engine bug (plan.md rule 5). Fixing
this de-quarantines bubble_sort3 (quarantined on cost, 137 s vs 30 s
limit).

Cost profile (measured; details in notes/regression-history.md and
git history of the arc): `bitvector_terms_proven_equal_for_memory_
resolution` entered 564 888 times, 95% returning false — the cost is
a failing search over the fact set (`bitvector_terms_equal_from_facts`,
`exact_condition_value` twice per call), NOT snapshot comparison
(only 6 of 540 k top-level comparisons are load-vs-load; memory-DAG
arms cannot reach it). The UpperBoundSplit is not where the time is.

**Lead to try first:** the replay re-derives exactly what the smart
planner derived one call earlier — the two run halves are the same
derivation twice. Cache/reuse the planner's result for the replay.

Repro:
```
cargo run --quiet --bin click-profile -- --time-limit 10m --threshold 500ms \
  mdtests/bubble_sort3_two_pass_sorted.md
```

Done when: no SIMPLE entry over 500 ms in that profile and
bubble_sort3_two_pass_sorted de-quarantines inside the 30 s limit.
