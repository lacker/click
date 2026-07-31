# Invariant-closer replay: 65 s SIMPLE, 130x over budget

Status: done (2026-07-31)
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

## Resolution (2026-07-31, worktree-agent-a9cc86becdb8e01de)

The headline numbers above were stale by the time this task was picked
up: prior arc work had already brought bubble_sort3_two_pass_sorted
from 137 s down to ~3.5 s (profile total). What remained of THIS bug
was the same replay-twice shape at smaller scale: `close_invariants`
SIMPLE at 772 ms exclusive, 1.5x over the 500 ms budget — still the
only SIMPLE offender, still the budget breach keeping the quarantine.

Mechanism (the "lead to try first", confirmed by probe): both calls to
`c_loop_invariants_hold_at_back_edge_using` live in
`verify_one_loop_preservation_proof` (src/lang/click/proof.rs). The
planner half calls it per context before emitting `close_invariants`
into the leaf certificate; the certificate-replay half then calls it
again per replayed context. An env-gated probe showed the replay
contexts' `(state, pure_facts)` are byte-for-byte equal to the planner
contexts' (exact Vec equality, not just set equality). Fix: the
planner half records each positive result keyed by the exact
`(CState, Vec<Proposition>)`; the replay half skips the re-derivation
only on an exact-key hit. `loop_entry_state` and `invariant_checks`
are the same objects for both halves by construction, so the key
covers every varying input. Soundness: the closer is a deterministic
function of its inputs; only Ok results are recorded; any input
difference at all falls through to the full check — a would-fail
replay cannot become a pass. `CLICK_DISABLE_CLOSER_REUSE=1` restores
the old double-derivation for A/B.

After: profile total 2.06 s, SIMPLE 46 ms (no SIMPLE entry over the
400 ms threshold used), mdtest passes in 2.16 s with budgets enforced.
De-quarantined in tests/mdtests.rs; all three gates green.

Noted in passing (NOT this task, pre-existing at clean HEAD):
`bubble_pass3_max_suffix.md` fails under MDTEST_FILTER in
`bubble_pass3.max_at_end` — "planned `simp` context premise is not an
available source fact" — matching its standing quarantine entry
(certificate-spelling surface, owned by that workstream).
