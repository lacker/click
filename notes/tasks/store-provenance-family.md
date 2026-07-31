# store-provenance family — acceptance corpus & per-member frontiers

Status: open (corpus record; members move as fixes land)
Claimed:

This file is the failure corpus for the named-memory-states arc
(`named-memory-states-arc.md`) **and** the current per-member frontier.
As of 2026-07-31 (arc stages 1–5 landed), every remaining member fails
on something that is *not* a load-equality question — do not chase these
into the arc; each diagnosis below was measured.

## Cleared (for the record)

- lib `verifies_old_memory_loop_invariant` — passes, un-ignored (arc
  stage 2a: `old(...)` now names function entry).
- mdtest `fill_tail_keeps_first.md` — de-quarantined (same fix).

## Remaining members, 2026-07-31 frontiers

- **mdtest `bubble_sort3_two_pass_sorted.md`** — **passes** at 137 s vs
  the 30 s limit; quarantined on cost. 65 s of it is a slow SIMPLE
  invariant-closer replay: an engine bug, tracked in
  `slow-simple-engine-bugs.md`, not here.
- **mdtest `bubble_pass3_max_suffix.md`** (~12 s) — certificate
  lowering: the planned `simp` context premise (the loop-exit invariant
  `ForAll`) is not an available *source* fact. Looks like arc work and
  is not: its two loads sit in the **same snapshot**, differing only in
  the index term. The two-pass version of the same program does not hit
  it.
- **mdtest `composite_resource_vector_fill_loop_snapshot.md`** (~48 s)
  and **mdtest `field_derived_precise_effect_after_metadata_write.md`**
  (~198 s, was 487 s before arc stage 4) — same failure class: grouped
  `simp` cannot certify its complete claim transition (vector_fill at
  `contract` path 0 tactic 2 for `ensures_2`; field_derived also carries
  a 29 s simple `fold`, tracked in `slow-simple-engine-bugs.md`).
- **mdtest `composite_resource_owner_buffer_field_dependent.md`**
  (~6 s) — "execution proof for `set_owned_first.ensures_0` changed
  more than the certified ghost-resource representation".
- **example `owned-vector`** (~13 s) — `vector_replace_if.contract`
  tactic 8 `have` cannot find `Implies(replace == 0, new == old)`. A
  propositional gap over plain variables; the goal contains no memory
  at all.
- **example `owned-string`** (~2.6 s) — the `terminated_at` smart-have
  unfold cannot discharge `loadable(data[len])`: a permission-plumbing
  question, not an equality one. (Earlier attempt recorded: feeding
  `replay.effect_facts` into planning did not help — stores are
  execution facts, not effect summaries; reverted.)

## Related, not quarantined

`mdtests/proof_advance_pointer_local.md` carries an explicit
`have at(statement(1).exit, selected) == ...` because certificate
generation cannot synthesize a point-qualified spelling for a local
pointer (the `advance` abstracts it into a fresh symbolic block; no
recorded program-point state binds the local to the abstracted value —
teaching `synthesize_surface_pointer` to look up pointer-valued locals
was measured not to help). When generation can find that spelling,
delete the `have` and confirm.

## Repro

```
CLICK_RUN_QUARANTINED=1 MDTEST_FILTER=<name> cargo test --test mdtests
CLICK_EXAMPLE=owned-vector cargo test --test examples
./target/debug/click-verify examples/owned-string/owned_string.click
```

Bound field_derived with `MDTEST_TIME_LIMIT` and keep it out of loops
(~200 s to fail); bubble_sort3 takes ~137 s to pass.

Done when: all members above de-quarantine / pass, and
`proof_advance_pointer_local`'s explicit `have` deletes cleanly.
