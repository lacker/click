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

## Morning session 2 (2026-07-30, master cf04159): TWO failures remain

Fixed loop_stdlib_permutation_invariant (cf04159): canonicalize_atomic_loads
now canonicalizes If conditions (depth-propagated via
condition_with_canonical_loads_with_depth); proves/proves_atomic accept
canonically-equal Bitvector32Equal goals and resolve load equalities via
the memory-resolution prover (reentrancy-guarded, depth-gated at 64 via
bitvector_term_deeper_than); mdtest/example harnesses give children 64MB
stacks (prover recursion legitimately exceeds defaults on snapshot-heavy
fixtures — three separate stack overflows during development all traced to
structural recursion on deep terms, always guard + gate new arms).

Remaining two and exact frontier state:

- composite_resource_vector_fill_loop_snapshot: branch
  `claude/forall-extension-wip` holds a nearly-complete forall
  bound-extension rule (forall v<b + final-index → forall v<b+1) for the
  kernel back-edge closer, plus invariant_closer_facts threading effect
  facts + store equations into both closer call sites (proof.rs) and a
  guarded PointerOffsetEqual resolution arm. Probes: decompose ✓, bounds
  goal==succ ✓, conclusions align below bound ✓ (compared under v<b),
  final-index conclusion ✗: `load(m_backedge, owner+4) == v1` does not
  prove even with store equations in context — next probe is whether the
  materialized store cell's key spelling (data-relative) defeats
  known_value/cell-search in bitvector_terms_equal_for_memory_resolution,
  or whether the assumed instantiated PointerOffsetEqual premise fails to
  reach the pointer-equality path. Dumps: /tmp/click-extend-*.txt.
- field_derived_precise_effect_after_metadata_write: ensures still do not
  derive from the full certified context even with the resolution arms
  (minimal derivation returns None; ~570s run). Needs the same
  load-resolution chain plus the grouped-simp candidate-loop perf work.

## Status after option (b) implementation (2026-07-30 morning, master 24ad60b)

Owner picked (b): everything gets a surface spelling. Landed: 26972e7
(postcondition premises spelled via recorded lowerings / exact-lowering
ambient facts / synthesized at(point,...) spellings, self-checked with the
exact tactic-replay check, which now tries raw premise spellings before
normalizing — fixed fill_n_segment_invariant) and 24ad60b (loadability
from assumed load-mentioning facts at leaf/forall/nested-exists levels —
fixed cstr_stdlib). THREE failures remain:

- field_derived_precise_effect_after_metadata_write: probe shows
  minimal_proposition_derivation over the FULL certified context
  (available + effect facts + store equations) returns None for its
  ensures — a prover-capability gap (needs load(m_out,len) resolved
  through the materialized len cell, then arithmetic with index==old);
  plus the known ~500s perf problem (grouped-simp candidate loop).
- loop_stdlib_permutation_invariant: initialize `have` cannot establish a
  quantified counting fact with If-terms over loads (Fold/If counting
  prover gap).
- composite_resource_vector_fill_loop_snapshot: kernel back-edge closer
  (verify_invariant_checks_at_back_edge_using) cannot re-derive the
  preserve-phase quantified conclusion across the iteration's stores.

De-quarantine reminder: mdtest QUARANTINED (4 entries) and examples
QUARANTINED (5 entries) still pending; lib is fully de-quarantined except
7 expansion tests (#[ignore]) that fail from the WIP-era changes.

## Status at end of overnight run (2026-07-30, master 5e8b8fb)

Landed: field layout-slot ownership (d523e42, fixed
hidden_separate_projection), CMemory interning (ebe44f1, lib suite 2x
faster), assumption-free canonicalization memos (4ff2be8), endpoint/base
load bridging (928a6eb, opens field_derived's fold gate; reentrancy
guard 5e8b8fb), five lib tests de-quarantined (7dae13f — default lib
suite now 464 green). Quarantined mdtests (4) and examples (5) retested:
none pass yet; one quarantined example overflowed the stack through the
bridge cycle (now guarded). The five visible mdtest failures all reduce
to the certificate-spelling design question below — awaiting the owner's
pick before more code. field_derived also needs the grouped-simp
candidate-loop perf work regardless (runs ~420s; hot loop is
atomic_derivation_premises candidate iteration under
pointers_proven_disjoint_by_explicit_range).

## Overnight findings 2026-07-30 (post-interning)

Interning + memoization landed (ebe44f1, 4ff2be8; lib suite 2x faster) and
endpoint/base load-bridging landed (928a6eb; opens field_derived's fold
gate). The remaining five failures converge on ONE design question:

**Effect-backed postconditions cannot be spelled in a pure surface
certificate.** field_derived's `ensures owner->len == old(owner->len)+1`
and fill_n's segment ForAll both DERIVE from the certified context
(available + statement effect facts + certified_store_equations — verified
by probe), and `ExactPropositionDerivation` replays them deterministically,
but `TacticCertificate::from_proof_tactics` rejects that tactic: the
b27015a hardening requires certificates to round-trip through the Surface
Click parser, and a kernel derivation has no source spelling. Options:
(a) admit kernel-derivation certificates into the certificate format
(breaks "expanded proofs are canonical Surface Click" — needs owner
sign-off); (b) synthesize surface At-point spellings for store equations
(e.g. `at(statement(k).exit, owner->len) == index + 1` is spellable — the
premise-expression search in the postcondition lowering would need to
synthesize At spellings the way the loadability-obligation block does);
(c) route these claims through the statement-transition layer (StepUsing
carries certified prerequisites without spelling them). (b) is the most
consistent with the existing design. **Owner picked (b) 2026-07-30:
everything gets a surface spelling.** A synthesized-TransportUsing fallback
for survives-writes goals was implemented and reverted: these ensures are
post-store facts, not transported facts, so it never fired.

## Related open questions (not part of A)

- `composite_resource_owner_buffer_hidden_separate_projection`: the ensure
  wants `separate(owner[0..2], data-range)` but hidden projection emits
  separations only for the *owned fields* — intervals [0,1) and [2,4)
  can't cover [0,2) (element 1 is struct padding). Language-semantics
  decision: should field ownership project separation for the full
  field-to-field span (including padding), or should the test change?
