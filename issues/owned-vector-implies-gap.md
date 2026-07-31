# owned-vector: have cannot find Implies(replace == 0, new == old)

Example `owned-vector` (quarantined in tests/examples.rs) fails in
~13 s at `vector_replace_if.contract` tactic 8: a `have` cannot find
`Implies(replace == 0, new == old)` — a propositional gap over plain
variables; the goal contains no memory at all.

History (bisected 2026-07-31): originally broke 07-19 at `9ea6739`
"remove replay bookkeeping tactics" (deleted RecordExecutionPoint /
ResetOpaqueCallCounter and reworked replay); two later events layered
on top, and the current failure site was introduced by edits made on
top of the already-broken example. Fix forward from the current
message; the deleted bookkeeping says where replay context may have
thinned. Retest after certificate-spelling-gap lands — the site may
move.

Also parked here: this example's PASS time exploded 1 s -> ~190 s
between 07-15 and 07-19 before any breakage — profile once it verifies
again.

Repro: CLICK_EXAMPLE=owned-vector cargo test --test examples
