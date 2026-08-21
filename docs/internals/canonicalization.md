# Canonicalization

Click needs one logically grounded model for when two terms denote one
value. This page is that model: which differences between terms are
definitional, which need a proved equality, and how the kernel records its
choice. The consolidated gap analysis and its acceptance criteria live in
`issues/canonicalization.md`; this page documents the contract the
implementation is converging on and the part of it that is already
enforced. Vocabulary follows the [glossary](../reference/glossary.md):
*term*, *kernel variable*, *load variable*, *snapshot*, *fact*.

## Why canonicalization exists

Symbolic execution produces a new snapshot at every statement. A read of a
memory cell is a term, `load(snapshot, pointer)`, that embeds the snapshot
it was read from — so one unchanged cell is read through many different
terms over a proof. Canonicalization collapses those reads onto *which
write* of the cell they observe: every read between one write and the next
maps to the same term, and a new term appears only when the cell actually
gets a new value.

## Two proof authorities

Every claim that two terms denote one value rests on exactly one of two
authorities. The distinction is load-bearing and must stay explicit.

**Definitional equality** needs no evidence. Two terms are equal by
definition when their difference is bookkeeping that symbolic memory
introduced: a cell whose value the snapshot already records, a snapshot
carrying cells or blocks the load cannot observe, or a chain of recorded
snapshot derivations that provably left the loaded cell alone. Verifiers
and replay accept equality of canonical forms directly.

**Proved equality** covers everything else: an assignment such as
`index == old(owner->len)`, a store crossing justified by pointer
distinctness, an arithmetic bound. These require a fact in the proof
context or a certificate, and any use of one in a derivation must be
expressible as a replayable simple step. No comparator, tactic, or search
may silently consume a proved equality while answering a question that
should be definitional.

## The canonical form

The single entry point is `canonical_term` (with `canonical_offset_term`
for pointer offsets). It rewrites only memory loads; arithmetic structure,
operand order, and the proof context are never consulted. It is a fixed
two-stage composition:

1. **Resolve or shrink each load** (`canonicalize_atomic_loads`): a load
   whose snapshot records a value for its pointer becomes that value; every
   other load keeps only the part of its snapshot the load can observe —
   the pointer's block plus the havoc markers. Loads inside the pointer's
   own offset are treated the same way.
2. **Replace each remaining load with its load variable**: the kernel
   variable identified by the cell and the snapshot of its last write, found
   by walking the memory derivation DAG.

The composition is deterministic, idempotent, and memoized at both stages.
Its result does not depend on where the term came from: a premise, a goal,
a resource-range endpoint, or a nested pointer offset canonicalize
identically. Load-variable substitution stops at binder scopes (`RangeFold`
bodies), where a load may mention bound variables; the first stage still
applies there.

## Load variables are the canonical form of a load

A load variable is the canonical form of the load it stands for, not an
alias for it. The load term carries an entire interned snapshot; the
variable is small, stable across snapshots that leave the cell alone, and
content-addressed so that independent producers (symbolic execution,
contract lowering, spec evaluation) introduce the same variable without
shared allocator state. Comparison and indexing therefore work over load
variables.

Two consequences:

- **Every load variable carries a defining fact.** Introducing one pushes
  the kernel-certified fact `v == load(snapshot, pointer)` into the path's
  facts. The defining fact is the only bridge from the variable back to
  memory content, and it is an ambient truth, not a premise a proof must
  re-derive.
- **A consumer never expands a load variable back into its load.**
  Expanding reinflates terms with snapshots, makes comparison cost depend
  on snapshot size, and reintroduces exactly the instability the variable
  exists to remove. The registry that detects id collisions is bookkeeping;
  registry membership alone is never proof that two terms are equal.

Load variables are ordinary kernel variables distinguished only by a
reserved id range, not by type. Their ids are opaque hashes; a certificate
refers to one through a snapshot form such as `at(statement(3).entry, x)`
or `old(x)`, and diagnostics print one by looking up the load it stands for.

## What is enforced today

- `canonical_term`, `canonical_offset_term`, and `canonical_condition_fact`
  are the comparison form: `terms_match_modulo_canonical_names` and
  `offsets_match_modulo_canonical_names` answer exactly by canonical-form
  equality (with a load-free fast path, since load-free terms are fixed
  points). Regressions live in `src/kernel/tests/canonicalization_tests.rs`.
- **Comparison-side keying is canonical throughout the availability
  boundary**: the explicit-equality graph keys its vertices by
  `canonical_term` (`equality_graph_term_key`), affine cancellation keys
  its atoms by `canonical_term` (`collect_affine_bitvector_terms`), the
  signed-order-bounds index is keyed under each fact's own endpoint term
  and its canonical form, and the exact frame-containment matchers compare
  goals and available facts by `canonical_condition_fact`. A load and the
  load variable for it are therefore one vertex, one affine atom, one bound
  entry, and one fact. This keying is deterministic and assumption-free, so
  exact certificate replay is unaffected.
- The arithmetic provers join by canonical form: the memory-resolution
  equality's deep arm compares full canonical forms, the increment and
  decrement overflow helpers match bases canonically, and
  `canonical_bound_holds` answers single-fact range bounds from the index
  before any searching arm runs.
- Certificate evidence follows the implicit-join design: a typed
  derivation cites its premise as the exact fact, while the tie between
  that premise and a differently written goal base is a canonical
  comparison — definitional, deterministic, and therefore replay-identical.
- Symbolic execution introduces load variables for loaded **pointers**
  (`canonicalized_pointer_value_from_int_cell`,
  `canonicalized_symbolic_load_value`), so a pointer loaded from an opaque
  cell never enters offset arithmetic as a load term, and its defining fact
  is emitted beside it.
- Surface synthesis resolves load variables it cannot otherwise express
  through the registry (`resolve_canonical_load_variables_from_registry`) —
  the sanctioned display direction: rendering a variable as source syntax
  is the printer's job, distinct from the forbidden comparison-side
  expansion.

## What is not yet enforced

Loaded **indices** still enter pointer offsets as load terms at the
remaining producer sites (C pointer addition, spec pointer-offset
evaluation, contract pointer arithmetic). Introducing load variables there
is implemented behind `CLICK_OFFSET_INDEX_LOAD_VARIABLES=1`
(`canonicalized_offset_index_term`), off by default. Two consumers still
assume load terms in those positions; both are recorded in
`issues/canonicalization.md`:

- a range check needing a two-fact bound chain falls past the indexed
  single-fact lookup into an unmemoized search and exceeds its budget; and
- across a call whose footprint may write a cell, the read before and the
  read after receive different load variables, and load resolution does
  not yet consult the proved equality between them.

Until those close, the switch stays off.
