# Canonicalization

Click needs one logically grounded model for when two terms denote one
value. This page is that model: which differences between terms are
definitional, which need a proved equality, and how the kernel records its
choice. The contract is enforced: terms are canonical at creation (the
`*_creates_only_canonical_terms` tests count violations over the example
projects and require zero). Vocabulary follows the
[glossary](../reference/glossary.md):
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
snapshot derivations that provably left the loaded cell alone. Proof checking
accepts equality of canonical forms directly.

**Proved equality** covers everything else: an assignment such as
`index == old(owner->len)`, a store crossing justified by pointer
distinctness, an arithmetic bound. These require a fact in the proof context,
and any use of one in a derivation must occur through a checked proof
operation with retained provenance. No comparator, tactic, or search may
silently consume a proved equality while answering a question that should be
definitional.

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

The composition is deterministic, idempotent, and complete over its explicit
input. Both stages and pointer-offset traversal use explicit worklists, with
work linear in the term they visit. A chain in which each materialized cell
stores a load of the next cell is followed iteratively too. Whole-term
memoization is used only after an iterative preflight establishes that the
recursive structural key is shallow; deeper terms bypass those caches and
take the same complete path. Thus a cache policy can affect speed but never
the canonical result. Narrow memory-DAG and load-identity caches remain keyed
by the identities they actually answer.

The result does not depend on where the term came from: a premise, a goal, a
resource-range endpoint, or a nested pointer offset canonicalize identically.
Load-variable substitution stops at binder scopes (`RangeFold` bodies), where
a load may mention bound variables; the first stage still applies there.

### Contextual vocabulary is an explicit proof operation

Creation sites do not rewrite a term to a preferred member of an equality
class. In particular, a verified call records its mutable ranges in
assumption-free canonical form in both the call-memory derivation and its
`CMemoryEffectSummary`. If a caller's effect or frame proof uses another
spelling for a bound, smart frame planning selects the exact equality premises
outside the kernel and emits an ordinary `frame using` certificate. The exact
frame checker consumes that proof-local range view without replacing the
stored summary.

The same rule applies to loads at propositionally equal addresses. Their load
variables remain distinct context-free forms. A target-directed congruence
derivation checks that both registered origins have the same memory epoch and
pointer block, and retains exact ground-equality paths for the differing
offset leaves. Smart proof expansion renders those paths as ordinary
`rewrite` steps followed by `normalize`.

Likewise, theory-aware normalization used only to group candidates in an index
is named for that purpose. Context-inconsistency checking uses a complete
order-endpoint index key plus necessary-condition residue keys: it follows the
entire finite endpoint and context-resolved load chain, while only comparing
theory-sensitive pairs whose residues intersect. These keys may admit extra
candidates but may not omit a pair accepted by the checked theory. They remain
context-local indexing, not canonical identity, because they consult proved
facts and do not satisfy the assumption-free contract above.

## Load variables are the canonical form of a load

A load variable is the canonical form of the load it represents, not an
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
- **Comparison never expands a load variable back into its load.** Doing so
  would reinflate terms with snapshots and make identity depend on snapshot
  size. A target-directed checked rewrite may inspect the two registered
  origins to establish address congruence, but it preserves the epoch and
  block and retains every equality premise. Registry membership alone is
  never proof that two terms are equal.

Load variables are ordinary kernel variables distinguished only by a
reserved id range, not by type. Their ids are opaque hashes; an expanded proof
refers to one through a snapshot form such as `at(statement(3).entry, x)` or
`old(x)`, and diagnostics print one by looking up the load it stands for.

## What is enforced today

- `canonical_term`, `canonical_offset_term`, and `canonical_condition_fact`
  are the comparison form: `terms_have_same_canonical_form` and
  `offsets_have_same_canonical_form` answer exactly by canonical-form
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
  exact checking is unaffected.
- The quantified-fact index uses an alpha-canonical structural key: logical
  binder identities and the accumulator/item binders inside a `range_fold`
  body are assigned deterministic ordinals while the key is built. Universal
  facts with the same shape therefore share an index entry even when lowering
  gave their binders different variable identities. Target-guided universal
  specialization can use matching signed-order, overflow, equality, and
  pointer conditions to propose symbolic arguments; each proposed argument
  and every substituted guard still needs an ordinary checked derivation
  before the fact is retained.
- The arithmetic provers join by canonical form: the memory-resolution
  equality's deep arm compares full canonical forms, the increment and
  decrement overflow helpers match bases canonically, and
  `canonical_bound_holds` answers single-fact range bounds from the index
  before any searching arm runs.
- Checked evidence follows the implicit-join design: a typed
  derivation cites its premise as the exact fact, while the tie between
  that premise and a differently written goal base is a canonical
  comparison — definitional, deterministic, and therefore identical across
  repeated verification.
- Symbolic execution introduces load variables for loaded **pointers**
  (`canonicalized_pointer_value_from_int_cell`,
  `canonicalized_symbolic_load_value`), so a pointer loaded from an opaque
  cell never enters offset arithmetic as a load term, and its defining fact
  is emitted beside it.
- Surface synthesis resolves load variables it cannot otherwise express
  through the registry (`resolve_load_variables_from_registry`) —
  the sanctioned display direction: rendering a variable as source syntax
  is the printer's job, distinct from the forbidden comparison-side
  expansion.

## Canonical at creation

Every term is canonical when it is created — by symbolic execution, by
lowering, and by contract evaluation: a memory load evaluates to its load
variable where it is born, with its defining fact beside it, so every
fact, offset, and range built from it is canonical and no consumer depends
on bridging between canonical and non-canonical terms. Comparison-time
canonicalization (`canonical_term`) remains as the definition of the form,
and the reasoning that views a load variable as the load it represents
(`viewed_as_memory_load`, `registered_load_for_variable`) is how consumers
keyed on load shape — substitution, quantifier triggers, frame checks,
loadability witnesses, and the quantified-fact index — see through the
variable.

A load variable is identified by its cell and the cell's *epoch*: the
snapshot the epoch walk (`cell_epoch_for_load_variable`) reaches from
the load's snapshot by crossing only edges proven, without assumptions, not
to write the cell — block declarations, cells forgotten, stores and call
havocs at constant-disjoint offsets or in distinct blocks. The walk runs on
the live snapshot before the canonical form restricts it, since the
restricted snapshot is a fresh intern with no derivation. Two snapshots
that reach one epoch produce the same load variable, and the frame checks'
endpoint matching (`memories_directly_match_for_pointer_load`) accepts
that identity, so a fact carried unchanged through several steps still
meets a later effect summary.

Two consequences are worth knowing when reading proofs. Where crossing a
write needs evidence (a havoc of `object(other)` against a pointer that is
only separate by a `requires`), the read before the call and the read after
it are different variables unless a step's frame check or an explicit
`transport` carries the fact across; facts never match across such an
effect structurally, and a step keeps the pre-step form of a carried fact
beside the carried one, since both stay true. And `old(x)` denotes the
entry value: it is the entry-epoch load variable, equal to the current
value only where that frame fact is established.
