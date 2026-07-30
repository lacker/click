# Canonical memory: plan of record (2026-07-29)

*Working note (see `notes/README.md`). Decision made with the repo owner:
interning now, named memory states later. Delete or fold into an issue once
the work lands.*

## Decisions locked 2026-07-29 (with repo owner)

- A first, re-land quantified-body bridging on top, C as eventual
  destination. Skip construction-time canonicalization (B).
- Thread-local arena; unbounded growth accepted; note in item-10 debt.
- Work lands directly on master in small validated commits (no branch).
- Intern `CMemory` only, at term-embedding boundaries; working CState
  memory stays a plain value.
- `Eq`/`Hash` by arena ID; `Ord` keeps same-ID fast path then structural
  comparison (raw-ID ordering would make BTreeMap iteration follow arena
  insertion order — nondeterminism risk in fuel-sensitive proof search).
- Globally memoize only assumption-free work (canonical_memory_for_pointer_load,
  canonicalize_atomic_loads) keyed by (memory ID, pointer);
  c_memory_load_is_unchanged is assumption-dependent — no global cache,
  gets fast via cheap equality; per-Assumptions cache is the fallback.
- Debug assertions that ID equality agrees with structural equality.
- Gates: zero regressions across all three suites; field_derived passes in
  the normal 30s budget; then attempt de-quarantine of the item-7 backlog.
- Padding semantics: owning a struct field covers its full layout slot
  including trailing padding (C intuition: padding belongs to the object).
  Fixes hidden_separate_projection via the projection emitting full spans.
  This one is independent of interning and can land first.

## The problem

`Bitvector32Term::MemoryLoad(Box<CMemory>, Box<Pointer>)` embeds a full memory
snapshot inside every symbolic load term (primitives.rs). Consequences:

- **Completeness**: two spellings of the same load — recorded at different
  program points, differing by irrelevant cells, local blocks, or havoc
  markers — compare structurally unequal. Everything the prover knows about
  bridging them lives in ad-hoc comparison-time machinery
  (`canonicalize_atomic_loads`, `memory_snapshots_match_for_resolution`,
  `c_memory_load_is_unchanged`, `c_memories_connected_by_effects`, ...).
  This is design-review item 11's correctness face and the root of the
  remaining mdtest failures and the item-7 quarantine backlog.
- **Performance**: giant terms as BTreeMap keys, deep-compared in linear fact
  scans on hot paths. `field_derived_precise_effect_after_metadata_write`
  runs >180s; `composite_resource_vector_fill_loop_snapshot` took 26s to
  *fail* and 590s when one more (correct) bridge was enabled.

## Options considered

- **A. Intern/hash-cons memories.** Arena of `CMemory` values; `MemoryLoad`
  holds an ID. Equality/hashing O(1); canonicalization and load-unchanged
  checks become memoizable per (memory ID, pointer). No semantic change.
  Doesn't itself prove more, but makes the existing correct bridging cheap
  enough to run where it's currently unaffordable.
- **B. Canonicalize at construction.** Prune irrelevant cells when building
  load terms (keeping havoc blocks — see soundness trap below). Kills most
  spelling drift, but changes term identity everywhere at once (whole-suite
  blast radius) and does nothing for the loop-invariant class, whose
  snapshots genuinely differ by real stores.
- **C. Named memory states.** `m1 = store(m0, p, v)`; havoc mints fresh
  names; loads reference names and equality becomes select-over-store algebra
  plus effect facts. The right endpoint — terms shrink by orders of
  magnitude and the loop class falls out naturally — but a rewrite of the
  memory model touching eval, resources, spec lowering, and `old()`.

**Decision: A now, C later. Skip B** (worst cost/benefit of the three).

## Plan for A

1. Intern `CMemory` behind an identity (thread-local arena accepted for now,
   consistent with existing thread-local use; note it in item-10 debt).
2. Memoize by (memory ID, pointer):
   `canonical_memory_for_pointer_load` (reasoning.rs),
   `c_memory_load_is_unchanged` (api.rs),
   `canonicalize_atomic_loads_with_depth` (api.rs).
3. Re-land the two bridges reverted purely for cost on 2026-07-29:
   - effect-chain equality inside `memory_snapshots_match_for_resolution`
     (reasoning.rs ~line 606): call `c_memory_load_is_unchanged` at
     depth <= 2 — this was *correct* but slow; the probe on
     `proof_advance_composite` showed the depth-gating issue (MemoryLoad
     comparisons enter at depth >= 1).
   - store-aware comparison inside quantified invariant conclusions for the
     back-edge closer (`verify_invariant_checks_at_back_edge_using`,
     loops.rs ~line 615): the preserve-phase goal's conclusion loads differ
     from the entry fact by the iteration's writes; equality needs
     read-over-write/frame reasoning, not premise weakening (a ForAll
     premise-weakening arm was tried: proved nothing, 26s -> 590s).
4. Expected to clear: `fill_n_segment_invariant`,
   `composite_resource_vector_fill_loop_snapshot`,
   `loop_stdlib_permutation_invariant`, `cstr_stdlib`, the
   `field_derived_precise_effect_after_metadata_write` timeout, plus most of
   the item-7 quarantine backlog (4 mdtests, 12 lib tests, 5 examples).

Key diagnostic facts for whoever implements this:

- `fill_n`'s postcondition ForAll **derives from the full available set**
  (probe: full_derives=true) but the derivation leans on ambient
  `CMemoryMutatesOnly` facts, which are excluded from
  `context_premises` (`proposition_has_contextual_derivation_rules`) and
  have **no surface spelling** — so surface `derive using` certificates
  cannot carry it; the certified-transition-fact route
  (`StepUsing`/`CertifiedFactTransport`) is the certificate story.
- SOUNDNESS TRAP: never drop havoc/call-havoc blocks from canonical load
  memories. Kernel test `memory_load_equality_does_not_ignore_loop_havoc_identity`
  guards this. Havoc blocks are semantic freshness markers.

## The ideal structure (C, for later)

A memory state is a name, not a value. States form a DAG:
`m0` (entry), `store(m, ptr, val)`, `havoc(m, region)`, `call(m, summary)`.
Loads are `load(m, ptr)`. Equality of loads across states is decided by the
store algebra (select-over-store, write-disjointness from effect facts) —
i.e., exactly what `certified_store_equations` and the effect-chain BFS
approximate today, but as *the* representation instead of a patch layer.
`old(...)` becomes a reference to a named earlier state instead of an
embedded snapshot. Most of the comparison-time bridging machinery gets
deleted rather than extended. Migration risk concentrates in eval.rs
(store paths), resource lowering, and everywhere `CMemory` appears in
`Proposition`/`Term` variants.

## Related open questions (not part of A)

- `composite_resource_owner_buffer_hidden_separate_projection`: the ensure
  wants `separate(owner[0..2], data-range)` but hidden projection emits
  separations only for the *owned fields* — intervals [0,1) and [2,4)
  can't cover [0,2) (element 1 is struct padding). Language-semantics
  decision: should field ownership project separation for the full
  field-to-field span (including padding), or should the test change?
