# The memory derivation DAG

The named-memory-states arc landed 2026-07-30/31. This page records what
the derivation DAG is, its invariants, what it bought (field_derived
487->198 s), the later block-allocation and cell-forgetting edges, and
the measured dead ends.

The original design brief and full regression experiment record were retired
from the working tree when this project wound up. They remain available in git
history as `notes/canonical-memory.md` and `notes/regression-history.md`.

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
  `CMemoryDerivation` edge such as `Store`, `LoopHavoc`, `CallHavoc`,
  `BlockDeclared`, `HeapAllocationPending`, `HeapAllocated`, or `HeapFreed`,
  each naming its
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

The same identity governs load canonicalization. The
materialization-source jump in `canonical_memory_for_pointer_load`
(replacing a memory whose same-block cells are all materialization
cells with their common source) re-adds the original memory's
`havoc:`/`call-havoc:` marker blocks after the jump: the surviving
cells witness only that *they* are unchanged since the source, never
that the loaded pointer is. Dropping the markers let a load be treated
as unchanged across a havoc that listed its own pointer as mutable;
`sibling_materialization_cells_must_not_launder_a_havoc`
(`src/kernel/tests/memory_dag_tests.rs`) pins the fix. Spellings that
legitimately differ only by marker-preserving materialization are
reconciled by the bounded per-cell matcher
(`memories_match_for_pointer_load_under_assumptions`), which requires
equal marker sets before comparing cells.

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
   `alias_guard_refuted_by_separation` in `PureFactContext::is_inconsistent`
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
   the original design brief named as the cost target. Two value-bridging
   snapshot-equality scans retired (92 lines) — honestly recorded as
   unreachable, not DAG-superseded (green with the flag off too).

**Why bubble_sort3 was immune to this arc** (three measurements, keep
before anyone re-attempts): only 6 of 540 k top-level comparisons are
load-vs-load; 95% of the calls return false, so answering earlier
cannot help a search whose cost is in not finding anything; and a
select-over-store arm fired **0 times in 295 290 lookups** — its loads
read a caller-provided symbolic buffer at symbolic indices, so there is
no store history to look up. Its historical 65 s cost was a separate
slow-simple engine bug, not arc work. The sampling trap is still worth
remembering: the hot frame was the fact-set-scanning *caller*, not the
canonicalizing arm it contained.

## Where the frontier is

There are currently no quarantined per-member failures. Future certificate
spelling, replay, or performance regressions should be diagnosed as focused
issues rather than treated as reasons to extend the DAG globally.

The heap slice adds `HeapAllocationPending`, `HeapAllocated`, and `HeapFreed`
edges. Successful allocation and free record the fresh/retired allocation
identity and exact, possibly symbolic extent. Consumers treat those two as
lifetime-changing boundaries: they may preserve unrelated snapshots, but must
never transport a load through the affected allocation as though allocation
or deallocation were an ordinary store. `HeapAllocationPending` records the
unresolved symbolic base and extent but changes no program-visible storage, so
the scoped loadability walk may cross it for every preexisting address. The
success edge starts at that pending snapshot. Failure removes the metadata and
structurally returns to the already-interned pre-allocation memory identity;
recording a backward edge there would violate the DAG's parent-before-child
invariant and is unnecessary.

## Landed 2026-07-31: fourth and fifth edge kinds, scoped consumers

The owned-string loadable work landed the punted block-allocation edge plus one
nobody had recorded:

- `BlockDeclared` — recorded by `CMemory::with_block`, NEVER for havoc
  marker blocks (`havoc:` / `call-havoc:` prefixes): a with_block-spelled
  marker must keep behaving like havoc
  (`conditions_equal_modulo_proven_snapshots_needs_frame_evidence`
  caught exactly this during development).
- `CellsForgotten` — recorded by `without_possible_aliasing_cells`, the
  write-path prune: same state, cache-forgetting only. The case-split
  prune (`without_cell` under an assumed-distinct branch) must never
  record one; its spellings agree only under the branch assumption.

**The critical scoping lesson:** the new edges plus the stronger
walks (separation-strength `Store`-hop crossing, stored-value pinning,
order-path DAG matching) CANNOT be enabled globally. Distinctness and
equality answers feed execution pruning, canonical load spellings, and
simp case-split structure, all of which certified sidecars replay
byte-for-byte; unscoped enabling broke owned-string's later functions
(pop_preserves_first: "planned simp context premise is not an
available source fact") and drifted Return-value spellings through
shared-fuel exhaustion. The power is therefore gated behind
`with_extended_dag_bridging`, entered ONLY by
`PureFactContext::proves_memory_loadable`; everywhere else the new edges
look exactly like the pre-arc absence of an edge. Fuel discipline
matters for the same reason: the hop distinctness runs under
`with_isolated_memory_resolution_fuel` so it cannot drain the
enclosing query's budget (fuel-coupled spellings must replay).

Session 1's displacement worry (first-wins letting a BlockDeclared /
CellsForgotten edge shadow a Store edge on content-equal snapshots) has
not bitten: both gate passes green in both DAG modes.

The initial implementation made owned-string take 5m26s to reach its next
failure. The resolved cost had three parts: proven DAG load equalities now live
in a generation-independent positive cache (only negative answers are retried
after an edge is added); four-byte loadability checks rank bounded
structure/DAG-matching ranges ahead of unrelated same-block ranges; and
certificate minimization declines optional general search over deeply nested
snapshot terms. The same run now reaches the separate certificate-spelling
frontier in about 10.4s. The regression test keeps several misleading
same-block permissions alongside the owned-string symbolic buffer range.

The old rationale, for reference: entry states and executing states sat
in **disjoint DAG components** ("arena identity is connected, arena
derivations are not"); the load-bearing deep-canonicalisation arm in
`bitvector_terms_equal_for_memory_resolution` still cannot be retired
(`loop_stdlib_permutation_invariant.md`), and
`load_unchanged_via_effect_chain` is still needed by owned-split-buffer
`Ensure(4)` — the new edges are consumed only inside the loadable
prover, so neither situation changed.

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

## Further work

The DAG arc itself is landed. Any future acceptance failures or performance
work should receive a focused file in `issues/`; do not treat this design
record as a live status board.

## Repro

```
cargo nextest run --lib --bins
cargo test --test mdtests
cargo test --test examples
CLICK_RUN_QUARANTINED=1 MDTEST_FILTER=<member> cargo test --test mdtests
CLICK_EXAMPLE=owned-vector cargo test --test examples
CLICK_DISABLE_MEMORY_DAG=1 <any of the above>   # A/B against the pre-arc path
```

Historical pre-optimization measurements were ~200 s for field_derived to fail
and ~137 s for bubble_sort3 to pass. Fixture gates now decide from deterministic
work budgets; neither wall-clock measurement is a correctness threshold.


## Edge kinds added 2026-07-31

`BlockDeclared` (a block came into existence; never recorded for havoc
marker blocks — that would launder freshness) and `CellsForgotten`
(the write path's possibly-aliasing cell prune; the branch-conditional
`without_cell` prune must never record one). These connected the
previously disjoint DAG components. The extended bridging power that
uses them is scoped via `with_extended_dag_bridging` to
`PureFactContext::proves_memory_loadable` only — enabling it globally
measurably changes certified spellings and simp case-split structure
elsewhere.
