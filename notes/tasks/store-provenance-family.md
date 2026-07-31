# store-provenance family — REGRESSIONS to fix (owner ruling 2026-07-31)

Status: open — in scope for the current project, not punted
Claimed:

**These used to work.** Every member was added green (2026-06-18 to
07-16) and broke during the 2026-07-25..28 strict-certificate wave
("enforce strict smart tactic certificates", "remove smart have
transport fallback", "Make expanded proofs canonical Surface Click"),
then was quarantined 07-29/30 already failing on master. They are
regressions from this project raising its own acceptance bar — for four
of them the prover still closes the claims and only the certificate
machinery cannot express the result. Owner ruling: fix them as part of
this project, as long as the fix stays straightforward; if one turns
out to need new surface semantics, bring it back to the owner instead
of brute-forcing.

**Attack per member: bisect first.** Each has a bounded window (its add
commit → 2026-07-29). Bisect to the exact breaking commit before
working the diagnosis; "certificate machinery gap" becomes "this commit
removed/required X". Add commits: bubble_pass3 78218b6, vector_fill
a28eb1c, field_derived d0f54fe, owner_buffer a3d00d3, owned-string
d2be685, owned-vector 45e7aea.

As of 2026-07-31 (arc stages 1–5 landed), every member fails on
something that is *not* a load-equality question — do not chase these
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
