# store-provenance / named-memory-states family

Status: parked (blocked on the canonical-memory arc — owner's call)
Claimed:

Scope: the one remaining failure family. Do NOT burn time re-bridging
individual spellings; the representation rewrite in
`../canonical-memory.md` is the intended fix.

Members (all diagnosed 2026-07-30):
- examples: owned-string (owned_string_push tactic 7: the terminated_at
  smart-have unfold cannot discharge loadable(data[len]); the bounds
  facts' load spellings differ from the goal's by direct-store
  provenance, and the planning assumptions carry no effect facts —
  adding replay.effect_facts did not help since stores are execution
  facts, not effect summaries; attempt reverted). Fails in ~9.6 s.
- examples: owned-vector (vector_fill.loop(0).preserve invariant closer
  missing a ForAll path goal). Fails in ~12 s (was a 600 s timeout).
- lib (1 `#[ignore]`, added 2026-07-30 from lib-ignored-expansion-tests):
  `lang::click::tests::verifies_old_memory_loop_invariant`. `fill_tail`
  carries `invariant p[0] == old(p[0])` across a body that does
  `p[i] = i` (i >= 1). The `loop(0).preserve` smart tactic certifies but
  cannot lower to a surface certificate: "no placement of the comparison
  operands at the 4 recorded program points lowered to the certified fact
  transport". Certified source loads `arg-memory + i*4` from a memory with
  *no* cells; certified target loads the same pointer from a memory
  carrying the store cells for `p[i] = i` and `local:i` — the load
  spellings differ by direct-store provenance exactly as in the
  owned-string case, and the 2026-07-30 framed-load-equality arm does not
  bridge it (`CLICK_DISABLE_CERT_ARMS=1` reproduces identically). Same
  program shape as the quarantined `fill_tail_keeps_first` mdtest below.
  Fails in 0.04 s. Repro:
  `cargo nextest run --lib --run-ignored ignored-only -E 'test(verifies_old_memory_loop_invariant)'`
- mdtests (6 quarantined): vector_fill, field_derived (named-memory-
  states residue) plus bubble_pass3, bubble_sort3,
  composite_owner_buffer_field_dependent, fill_tail_keeps_first —
  retested 2026-07-30, all still fail; bubble_* fail in the invariant
  closer with the same missing-ForAll shape.

- mdtests (1 rewritten, not quarantined, 2026-07-30):
  `proof_advance_pointer_local`. Its closer needs
  `selected == left or selected == right` about a local pointer that the
  `advance` at `statement(1).exit` abstracts into a fresh symbolic block.
  At function exit the only spelling is
  `at(statement(1).exit, selected)`, and certificate generation cannot
  synthesize a point-qualified spelling for a local pointer. The mdtest's
  proof now writes that `have` explicitly so the strict exit gate passes;
  the C source and the `ensures` claim are unchanged. When this family
  lands, delete that `have` and confirm generation finds the spelling.
  Measured dead end: teaching `synthesize_surface_pointer` to look up
  pointer-valued locals (as the scalar path already does) does not help —
  no recorded program-point state binds a local to the abstracted value.

Also related: grouped-simp candidate-loop perf
(atomic_derivation_premises clones whole Assumptions per candidate;
field_derived spent ~500 s there even to fail — recheck cost after the
decide memo before working on it).

Repro:
  ./target/debug/click-verify examples/owned-string/owned_string.click
  CLICK_RUN_QUARANTINED=1 MDTEST_FILTER=vector_fill cargo test --test mdtests

Done when: the canonical-memory arc lands and these de-quarantine, or
the owner green-lights targeted bridging work despite the arc.
