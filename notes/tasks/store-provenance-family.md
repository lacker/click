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
- mdtests (6 quarantined): vector_fill, field_derived (named-memory-
  states residue) plus bubble_pass3, bubble_sort3,
  composite_owner_buffer_field_dependent, fill_tail_keeps_first —
  retested 2026-07-30, all still fail; bubble_* fail in the invariant
  closer with the same missing-ForAll shape.

Also related: grouped-simp candidate-loop perf
(atomic_derivation_premises clones whole Assumptions per candidate;
field_derived spent ~500 s there even to fail — recheck cost after the
decide memo before working on it).

Repro:
  ./target/debug/click-verify examples/owned-string/owned_string.click
  CLICK_RUN_QUARANTINED=1 MDTEST_FILTER=vector_fill cargo test --test mdtests

Done when: the canonical-memory arc lands and these de-quarantine, or
the owner green-lights targeted bridging work despite the arc.
