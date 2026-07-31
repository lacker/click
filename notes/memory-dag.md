# Memory DAG record (reference, not a task)

Stages 1–5 of the named-memory-states arc, landed 2026-07-30/31: what
the derivation DAG is, its invariants, what it bought (field_derived
487->198 s), and the measured dead ends. The punted next increment
(fourth edge kind, block allocation) is recorded under "Next" — it
becomes a task only if an open work item needs it.

Design brief: `../canonical-memory.md`. Failure corpus and per-member
frontiers: `../regression-history.md`.

Scope boundary (owner, 2026-07-30): kernel/internal representation
only. No Surface Click syntax or semantics change. If the design seems
to demand one, stop that thread and record it under "For the owner".

## The problem

`Bitvector32Term::MemoryLoad(SharedCMemory, Pointer)` embeds a whole
memory *value* in the term, so two spellings of one location at two
program points are structurally different terms whenever anything
unrelated was stored in between. Every prover relating them bridges
values — deep canonicalisation, effect-summary scans, a BFS over
recorded effect facts — reconstructing at proof time the write history
execution already knew.

## The chosen shape: derivation-annotated interning

- The `SharedCMemory` arena (dense `u32` ids, already the `Eq`/`Hash`
  identity) *is* the name supply.
- Alongside each id we record how the snapshot was produced:
  `CMemoryDerivation::{Store, LoopHavoc, CallHavoc}`, each naming its
  base by `SharedCMemory`. Entry states have no derivation. That is the
  DAG, materialised. The `CMemory` value stays; readers retire one at a
  time.
- Provenance lives *outside* the value so it can never split identities
  (`Eq`/`Hash`/`Ord` stay derived and honest).

Two invariants make it safe:

1. **Advisory, never load-bearing.** A missing derivation costs
   completeness, never correctness; every consumer falls back to
   today's path. (Cross-thread handles resolve to no derivation —
   slower, not wrong.)
2. **Parent id < child id; first-wins recording.** A base must already
   be interned to be named, so cycles are unrepresentable (including
   store-of-same-value and store-then-store-back, which re-intern to
   existing nodes and keep the older derivation). Debug-asserted; every
   walk is hop-capped.

Havoc identity (the conventions.md soundness trap) is preserved at the
edge: walks cross `Store` only under proven pointer-distinctness,
`CallHavoc` only under proven range-disjointness, and **never** cross
`LoopHavoc` — loop havoc has no write set to be disjoint from.

Flag: `CLICK_DISABLE_MEMORY_DAG` skips every recording and every DAG
arm, restoring the pre-arc path exactly. Default on; the A/B handle.

## Landed (stages 1–5, 2026-07-30/31)

1. **Representation + recording** at the three edge producers
   (`CMemory::store`, `with_loop_memory_havoc`,
   `with_call_memory_havoc`); kernel tests pin the DAG shape.
2. **`c_memory_load_is_unchanged` DAG arm** — walks `after` down to
   `before` per the edge rules. Its leverage is histories the *net
   snapshot diff* cannot express (e.g. crossing a call-havoc marker
   that changes the block set); a single distinct store never needed it.
3. **(2a) `old(...)` gets a name.** Certificate replay resolved `old`
   positionally (region execution-start); the kernel lowering names
   function entry. `TacticReplayState::function_entry_state` +
   `old_reference_state()` make both sides name the same interned node;
   `at(function.entry, ...)` moves with it. Not flag-gated — it reads
   arena names, not derivations; a misresolution costs completeness
   only, because `find_candidate` still requires lowering-equality
   against the certified fact. Cleared `verifies_old_memory_loop_
   invariant` (un-ignored) and `fill_tail_keeps_first` (de-quarantined).
4. **(3) Two closer fixes**, neither a DAG consumer:
   `alias_guard_refuted_by_separation` in `Assumptions::is_inconsistent`
   (an assumed `PointerOffsetEqual(a, b)` contradicts recorded
   separation putting a and b in disjoint ranges of one block — uses
   plain `pointer_in_range`, NOT the memory-resolution variant, which
   refuses longer order chains), and
   `PropositionDerivationRule::UpperBoundSplit` (assumed `k <= b`
   splits a goal into `k < b` / `k == b`; goal-side, so no cross-
   snapshot fact matching; INT_MAX wrap is vacuously sound; depth 1).
   Moved every remaining corpus member off the invariant closer.
5. **(4) `memory_dag_cell_source`** — resolves one pointer against a
   snapshot by walking derivation edges backwards; undecidable hops
   stop and report the node, so two lookups compare by arena identity.
   Relates *sibling* snapshots through a common ancestor (two disjoint
   call havocs), which value bridging refuses outright. Wired ahead of
   snapshot comparison in `memory_loads_proven_equal`,
   `bitvector_terms_equal_for_memory_resolution`, both `proves` paths.
6. **(5) The measured verdict.** field_derived **487 s → 198 s**
   (2.46x), confirmed twice over: flag A/B on one binary (198 vs 592)
   and same-flag across the commit (487 vs 198). That is the member
   canonical-memory.md named as the cost target. Two value-bridging
   snapshot-equality scans retired (92 lines) — honestly recorded as
   unreachable, not DAG-superseded (green with the flag off too).

**Why bubble_sort3 is immune to this arc** (three measurements, keep
before anyone re-attempts): only 6 of 540 k top-level comparisons are
load-vs-load; 95% of the calls return false, so answering earlier
cannot help a search whose cost is in not finding anything; and a
select-over-store arm fired **0 times in 295 290 lookups** — its loads
read a caller-provided symbolic buffer at symbolic indices, so there is
no store history to look up. Its 65 s is a slow-simple engine bug
(`invariant-closer-replay-cost.md`), not arc work. Sampling trap recorded
there too: the hot frame is the fact-set-scanning *caller*; attributing
its cost to the canonicalizing arm it contains was already made once.

## Where the frontier is

Per-member diagnoses live in `../regression-history.md`. None of the
remaining failures is a load-equality question — certificate lowering
(bubble_pass3), grouped-simp claim-transition certification
(vector_fill, field_derived), ghost-resource representation
(owner_buffer), a memoryless propositional gap (owned-vector), a
permission question (owned-string).

## Next, if the arc continues: a fourth edge kind (block allocation)

Declaring a local creates a block but records no edge, so entry states
and executing states sit in **disjoint DAG components** ("arena
identity is connected, arena derivations are not"). Session 1 rejected
block-allocation edges as not worth it; the evidence now is stronger: a
load-bearing deep-canonicalisation arm in
`bitvector_terms_equal_for_memory_resolution` cannot be retired because
removing it reddens `loop_stdlib_permutation_invariant.md` — its two
snapshots differ exactly by one `local:i` block, unreachable by any
walk today. (Also load-bearing: `load_unchanged_via_effect_chain`,
needed by example owned-split-buffer `Ensure(4)`.) A fourth edge kind
is a new increment: it must be recorded at every block producer and it
risks displacing `Store` edges via first-wins on content-equal
snapshots.

## For the owner

*(nothing — no surface-semantics question has come up)*

## Dead ends (do not re-attempt without new evidence)

- Stage 1's load-unchanged arm moving `verifies_old_memory_loop_
  invariant`: never reached — candidate *placement* fails upstream.
- Validating `old`-resolution by a DAG ancestry walk: the chain does
  not connect (entry states are separate roots, see "fourth edge
  kind"), and it would be a weaker check than the certificate
  comparison already is.
- "The closer needs better load equality": three distinct causes hid
  behind that message (vacuous alias paths, a missing final-index
  split, certificate lowering) and none was load equality. Probe
  `decide(...)` on the two spellings before assuming otherwise.
- `pointers_proven_distinct_for_memory_resolution` for the alias-guard
  refutation: clears the mdtest, not example owned-vector; by-range
  true / memory-resolution false on the same facts.
- Raising the UpperBoundSplit depth to 2: +20 s, no outcome change.
  The 137 s is not in the split.
- A one-sided select-over-store equality arm: 0 firings in 295 290
  lookups (no store history for symbolic buffers); deleted.
- Feeding `replay.effect_facts` into closer planning: stores are
  execution facts, not effect summaries; no effect.
- From `claude/forall-extension-wip` (all rejected, session 1):
  `forall_fact_extends_bound_by_one` (fact-side final-index matching
  fails on exactly the snapshot drift this arc addresses — the
  goal-side UpperBoundSplit is the working replacement);
  `equality_graph_terms_match_with_facts` (right shape, pays
  value-bridging cost inside the hot equality graph);
  `invariant_closer_facts` (the effect-facts dead end above). The one
  piece worth a separate commit: `atomic_pointer_offset_equality_
  resolves`, resolution-aware `PointerOffsetEqual` — independent of
  this arc.

## Done when

The acceptance corpus in `../regression-history.md` passes: both
examples and all quarantined member mdtests de-quarantine, and the
explicit `have` in `mdtests/proof_advance_pointer_local.md` deletes
cleanly with generation finding the spelling itself.

## Repro

```
cargo nextest run --lib --bins
cargo test --test mdtests
cargo test --test examples
CLICK_RUN_QUARANTINED=1 MDTEST_FILTER=<member> cargo test --test mdtests
CLICK_EXAMPLE=owned-vector cargo test --test examples
CLICK_DISABLE_MEMORY_DAG=1 <any of the above>   # A/B against the pre-arc path
```

field_derived takes ~200 s to fail; bubble_sort3 ~137 s to pass.
Bound with `MDTEST_TIME_LIMIT`; neither belongs in a foreground loop.
