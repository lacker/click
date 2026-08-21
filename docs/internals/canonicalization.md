# Canonicalization

Click needs one logically grounded model for canonical proof terms. This
page is that model: which spellings are the same term, which changes need a
proved equality, and how a representative is selected and recorded. The
consolidated gap analysis and its acceptance criteria live in
`issues/canonicalization.md`; this page documents the contract the
implementation is converging on and the part of it that is already
enforced.

## Two proof authorities

Every claim that two differently spelled terms denote one value rests on
exactly one of two authorities. The distinction is load-bearing and must
stay explicit.

**Representational identity** needs no evidence. Two spellings are
representation-identical when their difference is bookkeeping the symbolic
memory introduced: a cached (materialized) cell standing in for the term it
caches, a snapshot carrying cells or blocks the load cannot observe, or
snapshot drift along recorded derivation edges that provably left the
loaded cell alone. Identifying such spellings is definitional; verifiers
and replay accept equality of canonical forms directly.

**Proved equality** covers everything else: an assignment equality such as
`index == old(owner->len)`, a store crossing justified by pointer
distinctness, an arithmetic fact. These require an explicit fact in the
proof context or a certificate, and any use of one in a derivation must be
expressible as a replayable simple step. No comparator, tactic, or search
may silently consume a proved equality while answering a question about
representational identity.

## The canonical form

The single entry point is `canonical_term` (with `canonical_offset_term`
for pointer offsets), defined as a fixed two-stage composition:

1. **Structural canonicalization** (`canonicalize_atomic_loads`): every
   load atom resolves its cached cell to the cached value, and every
   remaining load rewrites its embedded snapshot to the canonical memory
   for that pointer — the restriction to what one atomic load can observe,
   with havoc markers preserved.
2. **Canonical-name substitution**: every load atom that survives stage 1
   is replaced by its canonical load variable — the content-addressed name
   derived from the cell's derivation-DAG epoch and pointer.

The composition is deterministic, idempotent, and memoized at both stages.
Its result does not depend on where the term came from: a premise, a goal,
a resource-range endpoint, or a nested pointer offset must canonicalize
identically. Name substitution stops at binder scopes (`RangeFold`
bodies), where a load may mention bound variables that name no load
identity; structural canonicalization still applies there.

## Names are the canonical direction

A canonical load variable is the canonical spelling of its load, not an
alias for it. The raw `MemoryLoad` term carries an entire interned
snapshot; the name is small, stable across representational drift, and
content-addressed so that independent passes (contract lowering,
requirement evaluation, body execution) mint the same name without shared
allocator state. Comparison and indexing therefore work over names.

Two consequences:

- **Every canonical name carries an exact defining fact.** Minting a name
  pushes the kernel-certified equation `v == load(snapshot, pointer)` into
  the path's fact stream. The defining fact is the only bridge from the
  name back to memory content, and it is an ambient truth, not a premise a
  proof must re-derive.
- **A consumer never expands a name back into its load.** Expanding
  reinflates terms with snapshots, makes comparison cost depend on
  snapshot size, and reintroduces exactly the spelling instability the
  name exists to remove. The registry that detects name collisions is
  bookkeeping; registry membership alone is never proof that two terms
  are equal.

## What is enforced today

- `canonical_term` / `canonical_offset_term` / `canonical_condition_fact`
  are the comparison form: `terms_match_modulo_canonical_names` and
  `offsets_match_modulo_canonical_names` answer exactly by canonical-form
  equality (with a load-free fast path, since load-free terms are fixed
  points). Regressions live in `src/kernel/tests/canonicalization_tests.rs`.
- **Comparison-side keying is canonical throughout the availability
  boundary**: the explicit-equality graph keys its vertices by
  `canonical_term` (`equality_graph_term_key`), affine cancellation keys
  its atoms by `canonical_term` (`collect_affine_bitvector_terms`), and the
  exact frame-containment matchers compare goals and available facts by
  `canonical_condition_fact`. A raw load spelling and the canonical
  variable naming it are therefore one vertex, one affine atom, and one
  fact — spelling-blind by construction rather than by per-query bridging.
  This keying is deterministic and assumption-free, so exact certificate
  replay is unaffected.
- Production evaluation gives loaded **pointers** their canonical names at
  birth (`canonicalized_pointer_value_from_int_cell`,
  `canonicalized_symbolic_load_value`), so a pointer loaded from an opaque
  cell never enters offset arithmetic as a raw load, and its defining fact
  is emitted beside it.
- Surface synthesis resolves canonical names it cannot otherwise spell
  through the mint registry (`resolve_canonical_load_variables_from_registry`)
  — the sanctioned display direction: rendering a name as source syntax is
  the printer's job, distinct from the forbidden comparison-side expansion.

## What is not yet enforced

Loaded **indices** still enter pointer offsets as raw loads at the
remaining producer birth sites (C pointer addition, spec pointer-offset
evaluation, lang-side contract pointer arithmetic). The minting for those
sites is implemented behind `CLICK_OFFSET_INDEX_MINTING=1`
(`canonicalized_offset_index_term`), off by default.

The canonical joins extend through the arithmetic provers: the
memory-resolution equality's deep arm compares full canonical forms, the
signed-order-bounds index is dual-keyed under each fact spelling and its
canonical alias, and the overflow helpers match bases canonically — all
deterministic, so decisions replay. With those, footprint containment
under index minting proves.

The open blocker, recorded in `issues/canonicalization.md`, is
certificate provenance: derivations decided through canonical-form joins
do not yet record premises that reconstruct the decision on replay, so
contextual frame certificates fail to lower. Until derivation evidence
for canonically-decided steps replays, minting stays off by default.
