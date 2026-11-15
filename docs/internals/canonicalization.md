# Canonicalization

Click needs one logically grounded model for when two terms denote one
value. This page is that model: which differences between terms are
definitional, which need a proved equality, and how the kernel records its
choice. The persistent proof boundary is enforced: the
`*_creates_only_canonical_terms` tests count non-canonical condition facts
entering `PureFactContext` over the example projects and require zero.
Vocabulary follows the
[glossary](../reference/glossary.md):
*term*, *kernel variable*, *load variable*, *state*, *fact*.

## Why canonicalization exists

Symbolic execution produces a new state at every statement. A read of a
memory cell is a term, `load(retained_state, pointer)`, that embeds the state
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
introduced: a cell whose value the state already records, a state
carrying cells or blocks the load cannot observe, or a chain of recorded
state derivations that provably left the loaded cell alone. Proof checking
accepts equality of canonical forms directly.

**Proved equality** covers everything else: an assignment such as
`index == old(owner->len)`, a store crossing justified by pointer
distinctness, an arithmetic bound. These require a fact in the proof context,
and any use of one in a derivation must occur through a checked proof
operation with retained provenance. No comparator, tactic, or search may
silently consume a proved equality while answering a question that should be
definitional.

Return proposition certification permits an exact state to differ only by
recorded `CellsSeeded` steps that cache its own typed reads. Each step must use
load mode, match the element and value widths, and read bytes with the base's
producer-recorded read identity. The comparison walks only those added cache
steps to an identical state. Writes, havoc, forgotten knowledge, and
allocation changes remain barriers; read identity by itself does not establish
state equality or access authority. The end-to-end regression is
`mdtests/cached_read_return_completion.md`.
The same comparison preserves a selected resource body's identical readability
fact across cached states. Address, byte extent, and wide/narrow kind must
match exactly. Return-trace certification rechecks that body fact before
retaining its cached-state form; it never imports an arbitrary caller fact
context. Repeated comparisons of one state pair share a local result, so
checking multiple body facts does not repeatedly walk the same cache delta.

## The canonical form

The single entry point is `canonical_term` (with `canonical_offset_term`
for pointer offsets). It rewrites only memory loads; arithmetic structure,
operand order, and the proof context are never consulted. It is a fixed
two-stage composition:

1. **Resolve or shrink each load** (`canonicalize_atomic_loads`): a load
   whose state records a value for its pointer becomes that value; every
   other load keeps only the part of its state the load can observe —
   the pointer's block plus the havoc markers. Loads inside the pointer's
   own offset are treated the same way. When every observable cell is a
   materialization — it holds exactly the value a load of that cell reads
   from one common source state — the load is shrunk against that source
   instead, since such cells write nothing. The shrunk state keeps only the
   source cells the load's own state still holds: a source cell it lacks
   was erased since, by a havoc or a write, and carrying it across would make
   the named state record a value the cell no longer holds
   (`a_load_projection_jump_does_not_restore_a_havocked_cell`). A pointer cell counts when its
   value is the pointer a typed load of the same cell produces: the cell's
   block offset by that load's variable at the pointee's width. So owning a
   second descriptor, which materializes its pointer fields, does not rename
   a load of the first (`mdtests/unfold_region_then_write_a_descriptor_of_its_type.md`).
   A logical read of an integer cell (a Click expression, not C evaluation)
   does not take a recorded value, except a cell holding its own read: it
   keeps its version name, and the read-over-write authority relates it to
   the stored value ([spellability](spellability.md#a-read-names-its-version-point)).
2. **Replace each remaining load with its load variable**: the kernel
   variable identified by the cell and the state of its last write, found
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
class. In particular, a verified call records its owned ranges in
assumption-free canonical form in both the call-memory derivation and its
`MemoryEffectSummary`. If a caller's effect or frame proof uses another
spelling for a bound, smart frame planning selects the exact equality premises
outside the kernel and emits an ordinary `frame using` certificate. The exact
frame checker consumes that proof-local range view without replacing the
stored summary.

The same rule applies to loads at propositionally equal addresses. Their load
variables remain distinct context-free forms. A target-directed congruence
derivation checks that both registered origins have the same memory version and
pointer block, and retains exact ground-equality paths for the differing
offset leaves. Smart proof expansion renders those paths as ordinary
`rewrite` steps followed by `normalize`.

Likewise, theory-aware normalization used only to group candidates in an index
is named for that purpose. Context-inconsistency checking files order
endpoints under an index key (`order_endpoint_key`) that folds constants and
sorts addends. The key is context-free, but it is an index key, not
canonical identity: it groups candidates and is not the canonical form above.

Context-local ground equality is answered by the trusted equality graph
(`src/kernel/equality_graph.rs`): a congruence closure over pointer, offset,
int32, uint64, and registered load classes, described in
[Equality closure design](equality-closure.md). Consumers that enumerate
aliases or need premise-path evidence still use adjacency indexes over
canonical keys, with target-directed paths retaining the propositions that
justify each edge. Neither performs equality saturation or extracts a
preferred class member. Both are contextual indexes, not a replacement for
canonical form.

A theorem's written premise can carry more checked guards than its instantiated
requirement. `defined(a + b + c)` includes both additions' overflow guards;
`integer::int32_add_to_integer(a + b, c)` needs only the outer guard because its first
argument is already a bound value. Smart `apply` retains the whole written
premise and uses the explicit checker's shared listed-premise rule to select
its checked conjunct. It does not demand identical proposition structure or
import omitted evidence from ambient facts.

## Transitional load variables and shared reads

Scalar execution still introduces registered load variables for consumers that
have not migrated. Shared checker operands import those names as structural
`KernelTerm` reads. Address-index producers now retain shared machine operands:
a read index contains its state, address and read kind, rather than the
reserved variable. Offset hashing compares the shared child identity without
walking its read history. Canonicalizing an outer read preserves that child;
it must not resolve the index read to its cached value. Width/origin metadata
and scalar producers outside this boundary still use the registry.

The following describes the remaining registered-variable interface.

A load variable is the canonical form of the load it represents, not an
alias for it. The load term carries an entire interned state; the
variable is small, stable across states that leave the cell alone, and
content-addressed so that independent producers (symbolic execution,
contract lowering, spec evaluation) introduce the same variable without
shared allocator state. Comparison and indexing therefore work over load
variables.

Two consequences:

- **Every load variable carries a defining fact.** Introducing one pushes
  the kernel-certified fact `v == load(retained_state, pointer)` into the path's
  facts. The defining fact is the only bridge from the variable back to
  memory content, and it is an ambient truth, not a premise a proof must
  re-derive.
- **Comparison never expands a load variable back into its load.** Doing so
  would reinflate terms with states and make identity depend on state
  size. A target-directed checked rewrite may inspect the two registered
  origins to establish address congruence, but it preserves the version and
  block and retains every equality premise. Registry membership alone is
  never proof that two terms are equal.

Load variables are ordinary kernel variables distinguished only by a
reserved id range, not by type. Their ids are opaque hashes; an expanded proof
refers to one through a state form such as `at(region(3).entry, x)` or
`old(x)`, and diagnostics print one by looking up the load it stands for.

## What is enforced today

- `canonical_term`, `canonical_offset_term`, and `canonical_condition_fact`
  are the comparison form: `terms_have_same_canonical_form` and
  `offsets_have_same_canonical_form` answer exactly by canonical-form
  equality (with a load-free fast path, since load-free terms are fixed
  points). Regressions live in `src/kernel/tests/canonicalization_tests.rs`.
- **Comparison-side keys use the assumption-free canonical form throughout
  the availability boundary**: the explicit-equality graph keys its vertices by
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
  `canonicalized_symbolic_load_value_with_identity`), so a pointer loaded from an opaque
  cell receives a registered observation and its defining fact. Address-index
  producers import that observation into a shared structural read. The same function names every **integer scalar** it
  loads, one to eight bytes wide, signed or unsigned. Contract lowering
  already materializes a cell of any of those widths with
  `canonical_form_of_load`, so a width execution left unnamed would give one
  cell two terms — a load variable and a load term — that only the state
  relates, and a state the execution has since written no longer relates
  them. That is how a resource body fact about a cell an execution did not
  write survives a write to a sibling cell of the same node.
- **An `unfold` names the cells it exposes**, for the same reason and through
  the same projection contract lowering runs
  (`materialize_unfolded_instance_arm_cells` in
  `src/surface/proof/resources.rs`, which calls
  `project_selected_instance_arm_cells`). Contract lowering materializes the
  cells of the arm a section selects for a held instance; an unfold exposes
  the same cells one layer deeper and must adopt the same names, so the cell
  layout and element types are the ones already chosen there rather than a
  second convention. Arm selection uses the facts published by the rewrite.
  Pointer spelling uses the entry context plus the kernel's checked opening
  delta. For a parent with named children, that delta includes its direct
  pointer equalities between bare local names, established before naming the
  memory body and child arguments. Pure body facts retain their model bindings.
  The surface materializer uses the same delta; facts introduced later must
  not rename a scalar cell after its body equation was recorded. A fold still
  has to prove its proposed body facts
  (`mdtests/unfold_parent_alias_before_child_read.md` and
  `mdtests/unfold_parent_alias_does_not_assume_fold_facts.md`).
  Later reads use the indexed footprint coordinates of an existing cell,
  including reads through a C parameter newly equated with a model pointer.
  Exact cells retain precedence, and this coordinate choice grants neither
  read authority nor transport across a write
  (`mdtests/unfold_child_preserves_scalar_cell_identity.md`).
  Left unnamed, the unfolded body's facts keep the
  unfold-time version while a later C read of one of those cells walks its own
  version, and the two differ as soon as a store the assumption-free walk cannot
  cross lies between them — a write to a *separate* object, whose separation is
  a resource fact and not a DAG edge. The rbtree refold after
  `*new = *victim; rb_set_parent(victim->rb_left, new);` is exactly that shape:
  the child's word is read after the copy, and the fold's exact body-fact check
  needs it to be the variable the child's own arm spoke about
  (`mdtests/rb_replace_node_with_children.md`). Certification
  checks this without re-running the projection: an instance rewrite may change
  memory only by adding cells, and each added cell must hold the canonical load
  form of its own pointer at the pre-rewrite state
  (`memory_only_adds_named_cells` in `src/kernel/proof/execution.rs`), which is
  definitional and needs no search.
- **A checked guarded unfold names its exposed cells** through the same
  projection as an unconditional unmatched body. The kernel returns the guard
  case it checked; only an active body is materialized. Initial projection
  still leaves guarded bodies opaque, and an unknown guard cannot authorize
  an unfold. Naming adds the cell's canonical pre-rewrite load, not its model
  value, so a later write to that cell still invalidates the old field fact
  (`mdtests/c_guarded_resource_disjoint_store.md` and its negative controls).
- **Contract entry names an unmatched instance body's cells** too, without
  granting read authority: an unconditional, unmatched body is the one arm a
  held field-bearing instance always has, so `project_initial_composite_resource_cores`
  projects it as it projects a selected arm. A store to a separately owned
  object keeps those cells when the store opens the held instance one body
  layer (`docs/internals/resource-tracker.md`, "Two owners are two places";
  `mdtests/a_store_keeps_a_cell_a_folded_instance_owns.md`), so an `unfold`
  after the store reloads a pointer field at the name the instance was folded
  at, not at a fresh post-store name.
- Surface synthesis resolves load variables it cannot otherwise express
  through the registry (`resolve_load_variables_from_registry`) —
  the sanctioned display direction: rendering a variable as source syntax
  is the printer's job, distinct from the forbidden comparison-side
  expansion.
- **Naming cells makes terms a DAG, so rewriting must follow identity.** A
  load term carries a whole state and a state's cells hold further load
  terms, so one named cell per unfolded child nests states one level per
  child. Rewriting a variable therefore visits each *interned* state once,
  not once per path that reaches it: states are interned, so the rewrite of
  one is a pure function of its arena id and the substituted pair, and
  `substitute_bitvector_variable_in_shared_memory` keys this substitution's
  answers on that id. The curve is pinned by
  `variable_substitution_visits_each_state_once_per_rewrite`, and
  `click profile` charges the work to the named operation
  `substitution: state rewrite`.

Deep memory canonicalization preserves numeric seeded and state-copy runs
whose bases already have canonical form. Each numeric slot is minted as an
atomic load variable, which this normalization leaves unchanged; the source
need not be uniform. View adjacency likewise reads live run intervals as
contiguous byte regions, keeping holes excluded. Both operations depend on
stored representations rather than the numeric length of the range.

## Canonical at creation

“Canonical at creation” names a persistent-boundary invariant, not every
transient syntax tree a planner may allocate. Every ordinary condition fact
entering `PureFactContext` already equals its assumption-free
`canonical_condition` form; load-variable defining equations and certified
store equations deliberately retain the load syntax that states what they
define. The project regressions instrument this exact boundary while symbolic
execution, contract and spec lowering, resource projection, and call
application run. Persistent offsets, ranges, and call footprints likewise
canonicalize their load-bearing terms at their construction sites.

A memory load therefore becomes its load variable where a persistent fact or
identity is born, with its defining fact beside it. No consumer depends on an
implicit contextual rewrite between stored forms. Comparison-time
canonicalization (`canonical_term`) remains the definition of the form, and
the reasoning that views a load variable as the load it represents
(`viewed_as_memory_load`, `registered_load_for_variable`) is how consumers
keyed on load shape — substitution, quantifier triggers, frame checks,
viewability witnesses, and the quantified-fact index — see through the
variable. None of these creation paths chooses a member of a proved equality
class.

A load variable is identified by its cell and the cell's *version*: the
state the version walk (`resource_tracker::last_same_version_point`, through
`cell_last_same_version_point`, called from `load_variable_for_cell_with_origin`) reaches from
the load's state by crossing only edges proven, without assumptions, not
to write the cell — block declarations, cells forgotten, stores and call
havocs at constant-disjoint offsets or in distinct blocks. The walk runs on
the live state before the canonical form restricts it, since the
restricted state is a fresh intern with no derivation. Two states
that reach one version produce the same load variable, and the frame checks'
endpoint matching (`memories_directly_match_for_pointer_load`) accepts
that identity, so a fact carried unchanged through several steps still
meets a later effect summary.

Before the version walk runs, the load resolves against the state's own
materialized cells, and a cell holding a load variable answers the naming
query outright: that variable already names this value, so the load takes
it. This is what carries a materialized cell across an effect the walk
itself cannot cross. A call havoc keeps a cached cell only when the
assumptions at the call prove the callee's write set disjoint from it
(`ranges_proven_disjoint_from_pointer`), and certification re-checks that
retention, so the surviving cell is checked evidence rather than a second
alias approximation. A callback table read between two calls through it
stays one value this way (`mdtests/rb_augment_callbacks_helper_owns.md`);
drop the `separate` requirement and the havoc forgets the cell, the reload
is a new variable, and the contract established for the old one no longer
applies.

Two consequences are worth knowing when reading proofs. Where crossing a
write needs evidence and no cell was materialized before it (a havoc of
`*other` against a pointer that is only separate by a `requires`),
the read before the call and the read after it are different variables
unless a step's frame check or an explicit `transport` carries the fact
across; facts never match across such an effect structurally, and a step
keeps the pre-step form of a carried fact beside the carried one, since
both stay true. And `old(x)` denotes the entry value: it is the
entry-version load variable, equal to the current value only where that
frame fact is established.

Checked algebraic model equalities also participate in the shared equality
closure. Semantic fact lookup combines model aliases with checked constructor
cases and propagates equality through constructors and pure calls. This does
not unfold functions or compare match bodies under their binders. The
[typed model fragment](equality-closure.md#typed-algebraic-model-values) describes
the retained type distinctions and scope rules.
