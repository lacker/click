# Memory derivation DAG

Click interns kernel memory states and records how each new state was
derived. The resulting directed acyclic graph (DAG) lets memory reasoning
relate loads across stores, calls, allocation, and other state changes without
reconstructing the complete history from state values.

This is an internal representation. It doesn't add Surface Click syntax or
change which C programs Click accepts.

## Representation

`SharedMemory` is the stable identity of an interned `Memory` value. The
arena assigns dense identifiers. A separately stored `MemoryDerivation`
describes the edge from an already-interned parent to a child state.
Keeping provenance outside `Memory` means that equality, hashing, and ordering
continue to describe memory values rather than the route used to produce them.

Each map and set inside a state (`blocks`, `cells`, `union_cells`, the
ended-lifetime set, and every heap collection) is a `HashedOrdMap` or
`HashedOrdSet` from `src/kernel/primitives/persistent_map.rs`: a persistent
B-tree (`imbl::OrdMap` / `imbl::OrdSet`) that also carries a cached content
hash, the wrapping sum of one fixed-key hash per entry. A state therefore
shares structure with the state it came from: cloning a map is O(1), a
store copies only the O(log n) path it changes, and hashing a state reads
the cached sums instead of visiting its cells. The sum is independent of
insertion order, so equal contents hash equally however they were built.
Equality rejects on the state's O(1) content hash, accepts maps that share
a root, and otherwise compares elementwise, charging each compared entry to
the deterministic work counters. Ordering stays lexicographic over entries.

A rule applied at one address visits only the entries that can alias it.
Every state collection is keyed by a `Pointer` (or a key that orders by
one), `Pointer` orders by block first, and `PointerBlock` orders by variant,
so one block's entries are one key range, the `Symbolic` blocks are one range
and the `Heap` and `Temporary` blocks come last. `PointerBlock::proven_distinct`
separates a `Heap` or `Temporary` block from every other block except a
`Symbolic` one, so an access into an allocation can alias only its own block
and the symbolic range; any other access can alias at most the non-heap prefix
of storage the program declares. `AliasCandidates`
(`src/kernel/primitives/alias_candidates.rs`) names those key ranges, and the
store, call havoc and its checker, free, contract retirement, heap-status
queries, the load path and the load-observability comparisons all visit only
them. An entry outside the ranges is in a block proven distinct from the
access, so each of those rules already kept it (or answered `false` for it)
on the first rung of its ladder, and restricting the visit changes no answer.
Loop havoc stays whole-memory: its write set is every reachable cell. The
interface join does not. It keeps a cell, or a whole run, that every arm
holds with the same value, and it finds the rest by diffing the arms'
states, which share every subtree no arm touched. Its work is the entries
on which the arms differ, not the state
(`interface_join_does_not_visit_cells_its_arms_share`). A state that holds
a typed union view takes the whole-map pass instead, because a view is
forgotten whatever the arms agree on.

Interning looks up the caller's storage roots first, then the content. A
structural hit registers the caller's roots too, and the arena pins them so
the addresses cannot be reused by other content; asking again for the same
state is then a pointer-identity hit with no comparison.

Execution carries the arena's canonical storage forward. A producer interns
its input as the edge's base and continues from the base's stored instance
(`intern_derivation_base`), and `record_memory_derivation` replaces the
result with the stored instance of its content, an O(1) handle clone, so
every state a path carries, and every fact, term, or certified store built
from it, is the instance the arena holds. Equal states therefore share
their roots, and facts that embed them compare by root identity rather than
entry by entry; the recorded edges are unchanged. Because every result is
derived from its base's canonical storage, a statement executed twice from
one state (planned, then checked) is recognized as the base's recorded child
before any structural lookup: the arena indexes each base's recorded children
by content hash, and `Memory::eq_relative_to` compares the two results'
changes from the base (`HashedOrdMap::eq_relative_to`, which diffs against the
base and so walks only the changed paths). The answer is exact whatever the
states share; only the cost depends on the sharing.

The arena is per thread and per verification. Interning dedups by content and
keeps the first derivation recorded for an id, so two verifications sharing
one arena would let the second inherit the first's edges for any state
with the same content — a call havoc of a same-named callee, for example,
since havoc identities restart per verification. `VerificationSession`
(`src/kernel/mod.rs`), entered at the outermost verification boundary,
starts a fresh arena under a new token and empties every table keyed by
arena ids or holding arena states (the load registry, the canonical-form
caches, the reasoning memos, and the per-verification execution caches).
Memory states from an earlier session still compare by content but answer no
derivation query.

The producers in `src/kernel/primitives/memory_state.rs` record these edge
kinds:

| Edge | Meaning |
| --- | --- |
| `BranchJoin` | An abstraction of all incoming memories. A selected read crosses only when typed preservation paths connect every input to a common state; cache presence is irrelevant. |
| `Store` | One pointer was assigned a value. No fact context is recorded on the edge. |
| `LoopHavoc` | A loop may have changed memory; verified whole-loop effects carry a checked write set. That set also holds every automatic object, record or array, the body may write through a pointer: one the body names, a bare object name being its address, or one whose address a local or cell holds at entry. A set derived from the function's resources alone covers only memory the function was given (`a_loop_call_writing_a_local_struct_forgets_its_earlier_value.md`). |
| `CallHavoc` | A call may have changed the callee's owned ranges, and none of the memory its caller kept owning. |
| `BlockDeclared` | A new non-havoc block entered the memory model. |
| `ObjectInitializationRecorded` | Initialized-byte metadata was extended after writes already recorded in the DAG. Stored values are unchanged. |
| `CellsForgotten` | Standalone cache projection used by bulk producers and symbolic-read reduction. Ordinary scalar program stores perform invalidation internally and record only `Store`. |
| `HeapAllocationPending` | An allocation request has an unresolved base and extent but no successful storage yet. |
| `HeapAllocated` | A fresh allocation identity and extent became live. |
| `HeapFreed` | An allocation identity and extent stopped being live. |

Entry states have no parent edge. Failed allocation returns to the existing
pre-allocation identity instead of recording a backward edge.

The history root a proof path starts from (the empty memory, or the startup
state for a program-entry `main`) is the `function.entry` point. Entry
construction (declaring static storage and parameter objects, seeding resource
cells) is recorded on top of it and is no point of its own, so a version walk
that crosses it ends at the root (`HistoryEnds`), and a read of memory nothing
has changed since is spelled `old(...)`. Ordinary function entry declares
static storage (globals, static locals, their arrays and fields) without
contents: a read that finds no cell is a load at its version point, the root
when nothing wrote it, and a symbolic index into a never-written array is one
load whatever the array's length.

A scalar program store retains its original input before invalidating cached
values, records initialization and effective types, and interns only the completed
store. Cache cleanup is not a separate transition on this path. If invalidation
loses knowledge, the completed state retains the `ForgottenFrom` marker for
the original input; discarding a cached value must not make a post-write state
identical to an older state. The low-level store constructor used for already
prepared cells remains distinct from the program-store operation.

Unresolved scalar program reads name their actual input state, so an explicit
fact about that state matches the returned value. Temporary cache reduction can
resolve a read but does not choose the state named by an unresolved scalar
result. Pointer-read naming retains its existing projection and provenance
behavior; its cell-version naming walk is a separate removal target.

## Shared byte separation for stores

Cache preservation and read-over-store use
`indexed_store_byte_separation_evidence` for the same complete accesses.
Numeric-address classes retain one explicit pointer spelling per class, with
constant-displaced spellings preferred. Class merges update that witness in
local work; a query selects two witnesses without enumerating their classes.
Comparing their byte windows can establish separation or actual overlap.
Numeric equality supplies no pointer origin, ownership, or read permission.

If geometry is unknown, the checker queries stated separation by the two
nonempty anchors and checks that each range covers the entire corresponding
access. It does not scan the shared external-argument block's separation facts.
Owned compositions use the same full-access membership check, selected by the
two base addresses without an interior block scan. Known equal addresses or
partially overlapping windows take precedence over
separation authority. Evidence stays local to the fact context; a context without
the premise, or another branch, does not hold that authority.

## What a state's identity is

A state includes its known cells, the state it was forgotten from, and
the incoming identities of its most recent branch join.

Interning by content is what lets one node stand for every execution that
reaches it, and a load reads its name from the state it happens at. Both
rely on the content deciding the state. Known cells alone don't: dropping a
cached value leaves the memory unchanged and the knowledge of it gone, and a
cell map that has forgotten a store looks exactly like the cell map before
that store. After `a[i] = 7; a[j] = 0;` the second write drops the possibly
aliasing `a[i]` cell and the map is empty again, as it was at function entry.

So `Memory` carries a `forgotten_from` mark: the interned identity of the
state cached values were dropped from, part of equality, hashing, ordering
and the interning key. A state means "the memory the mark denotes, with
these cells known on top of it", so two executions reaching the same cells
over the same mark really are in the same state and interning stays sound,
deterministic and path-independent. An entry state carries no mark, so no
forget can land on one.

The mark is set where cached values go without the memory being known
unchanged, and only there:

- the write path's narrowing (`without_possible_aliasing_cells`) sets it for
  cells dropped because the store *may* alias them. A cell whose every byte
  the store writes is stale rather than forgotten — the store about to run
  replaces exactly what was dropped — so those alone leave no mark, and a
  sequence of writes to one cell mints no chain;
- the aggregate copy's `without_field_cells` sets it: nothing restores a field
  the copy could not carry;
- havoc keeps its own marker blocks, and an ended automatic lifetime its own
  tombstone. Both are already visible in the content, and neither needs a
  second mark.

Later stores carry the mark they were given, and so do the projections used
for load naming: the pointer-observable form may drop cells this load is
proven not to read, but not the mark.

An interface join retains the identities of all incoming states in
`join_inputs`, including through read projections. Two joins with empty cell
maps must not become the same state when their incoming histories differ.
The persistent set hashes incoming content hashes without recursively walking
their histories; equality also checks their exact arena identities.

A load's name is not usually this state's hash, because
`load_variable_for_cell_with_origin` first asks the resource tracker for the
cell's version point — the oldest point back to which the recorded steps show
this cell unchanged — and names the load there. A cell whose version the tracker can reach keeps the
name it had; the mark decides the name only where the walk stops. It decides
the *history* everywhere, which is the point.

A cell the state holds materialized is named by its value before any walk.
An integer cell holding a load variable resolves to that variable through the
canonical form. A pointer cell whose value is exactly the pointer a typed load
of that cell produces (the read's own `LoadedPointer` name at displacement
zero, defined at the same address) is that read, at its defining memory.
That is what keeps a struct field such as `arena->occupied` one name across a
loop head: the walk is assumption-free and stops at the head's havoc, while
the head's copy-back has already kept the cell's value because the checked
footprint is disjoint from it.

A scalar seeded run that caches loads from the same producer-maintained read
identity as its base does not change bytes. `SeededLoadsOfBase` carries that
local fact across the edge before slot selection: an exact slot match is a
cached read, not a new write or cell version. The same witness preserves a
read wider than a cached slot: two four-byte
loads of unchanged bytes do not partially overwrite an eight-byte pointer.
A real partial store remains a barrier before those cache-only edges.
Checking compares the source identity, load mode and exact scalar stride; it
never enumerates the run or assumes a caller's separation facts. Boolean and
pointer representations remain under their existing rules. Constant runs,
copies from another address, and loads from an older changed state cannot
use this witness. Thus opening a returned resource preserves unrelated caller
cells without hiding the call's preceding havoc.

Assumption-aware lookup also selects a run's slot compactly. Exact index
constants, stated pointer aliases, and indexed base aliases can identify one
live slot; a hole cannot supply its old value, and the selected cell must
match the load's width. Aliases known through recorded loads can propose one
slot from the constant offset difference; the full pointer matcher must
validate that candidate. If no slot is identified, the run remains a possible
alias unless its whole range is proved separate. An unknown symbolic index
never causes lookup to enumerate every element, including during refolding
and failed old-value searches.

Wide scalar reads use selected pointer equalities without entering the int32
congruence graph. Equal addresses give equal eight-byte reads in one state,
or when bounded history walks reach the same source node. Each walk retains
the full access width and stops after at most 64 edges. If the cheap address
classifier stops at a store, the full pointer matcher may identify that exact
store as the read's source, provided its value has the matching width. This
check neither searches earlier writes nor preserves an old value across a
whole or partial overwrite.

Seeded runs keep their source states, but do not retain named slot values.
Reading a slot goes through the load-naming cache scoped to the current
load-origin epoch. A reusable verification session retains the arena and its
runs across rechecks; returning a slot value cached inside a run would skip
the mint that refreshes the load's live origin, leaving transport without an
origin in the current function. The session-wide name remains unchanged,
while its first observation in each epoch records the live source again.

## Structural invariants

Every recorded parent identifier is smaller than its child identifier. The
parent must therefore exist first and a derivation cycle can't be constructed.
Recording is first-wins: if interning finds an existing equal memory value, it
keeps that node's established provenance.

An edge whose base is not older than its result is dropped, and a step dropped
that way is on no recorded history at all. For a step that lost knowledge that
is a false theorem waiting to happen — it is how the write to `a[j]` above came
to be recorded off the entry state, with the write to `a[i]` on no chain — and
the forget mark is what makes it unrepresentable, checked where the mark is
set. Where a step lost nothing, the older node is an ancestor whose history is
this path's own prefix: the load path's distinct-cell reduction drops only
cells the loaded pointer is proven distinct from, so every step between that
ancestor and here is one of those stores. `record_memory_derivation` counts
the edges it drops by kind, and the mdtest harness prints the corpus totals, so
a new producer that records its steps nowhere is named by a gate run.

Derivations are advisory evidence. Missing provenance can make a reasoning
query fail to establish an equality, but it can't make an invalid equality
true. Walks are bounded and fall back to the checked reasoning path
when an edge is missing or can't be crossed safely.

The graph never treats a lifetime boundary or an unknown write as an ordinary
unchanged store. In particular:

- a `Store` edge is crossed only with sufficient pointer-distinctness evidence
  checked in the querying proof context: distinct blocks or a decided
  common-base offset inequality, or full byte separation after re-expressing
  the store through the querying context's checked pointer-equality graph.
  The latter retains the selected address spelling and rechecks both its full
  pointer equality and the complete store/read widths; different addresses
  alone do not exclude partial overlap. No assumptions are captured on the edge,
  because first-wins interning lets paths with different assumptions share
  one edge, and one path's `length == 0` must not preserve another path's
  load;
- a `CallHavoc` edge is crossed only with sufficient range-disjointness
  evidence, likewise checked in the querying context, or when a range the
  caller kept owning outside the transfer holds the cell. Those ranges, and
  the facts of the residual instances they were opened from, are the edge's
  own. The write-set marker carries an exact canonical identity for the
  retained flat-owner set and spells its placement premises, so every path
  that shares the edge kept the same memory; placing the cell inside one is still decided
  in the querying context;
- a `LoopHavoc` edge with no checked footprint isn't crossed; a verified
  footprint is crossed with range-disjointness evidence or a selected
  withheld ownership range covering the full read;
- allocation and free preserve unrelated locations but don't preserve a load
  through the affected allocation;
- havoc marker blocks remain attached during materialization-source
  canonicalization, so materialized sibling cells can't hide a havoc, and the
  source's cells survive only where the projected state still holds them,
  so the source can't restore a cell the havoc erased.

These rules are soundness boundaries, not search heuristics.

A mutable range with structurally identical endpoints changes no bytes. The
`Empty` typed frame rule accepts it before any separation lookup, for signed
and native bounds and every read width. It does not assume bounds are equal
from facts or discard a nonempty range. In particular, an empty prefix carried
by a loop resource must not block transport of nested pointer reads.

For explicit separation facts, `SeparatedRangeEvidence` retains both selected
members and the complete read's membership. Checking authenticates those members
against the still-present fact, checks the whole mutable footprint is contained,
and checks full-width read membership and non-overlap. Starting inside a separated
range does not establish that a wider read ends inside it. The producer selects
separation buckets by the queried address blocks, avoiding a scan of all
proposition facts.

## Consumers and scope

Memory-load equality and unchanged-load reasoning use derivation ancestry to
find a common source state for a specific pointer. A query stops at an edge
whose safety condition it can't prove. Positive answers are cached by stable
state and pointer identities; failed answers can be retried after new
derivation information becomes available.

Exact-store lookup uses the maintained pointer equality graph, so a known
base alias also identifies the same field offset. The shared address predicate
still distinguishes other fields, and the value check still requires the
store and read to have the same width. It does not scan unrelated facts or
infer an alias from matching offsets in different blocks.

Explicit `normalize() using { ... }` can recover the value of a recorded
full-width pointer read. The query follows its exact retained canonical
projection source, when present, then at most 64 derivation edges in either
equality orientation. It uses the cited conditions to justify crossings and
compare the recovered value. If the cheap walk stops at a store whose address
needs recorded load identities, the bounded query checks that one endpoint with
the full pointer matcher and the exact typed width; it never searches older
writes at that point. Explicit `transport` uses the same read-value rule for
pointer and pointer-offset equalities. Whole-pointer equality checks the
complete stored pointer, including its block. Same-block pointer comparisons lower to offset
equality; that form uses an exact typed-read offset definition, including its
stride, and proves only the offset equality. Conflicting offset definitions
remain ambiguous. Equal offsets alone do not establish equality of blocks.
A narrow read, a scalar cell, or an intervening partial write cannot supply a
full pointer value. These rules establish only the selected equality and do
not grant ownership or initialization authority.

Explicit frame checking can stop at a `CellsForgotten` edge's retained input
value instead of skipping it and trying to cross an older loop footprint.
The query reads the exact address in that one predecessor and requires the
complete access width. A typed scalar observation that names the other
endpoint's canonical read supplies equality evidence; pointer representations
are excluded. The retained no-write path and the read kind remain part of the
certificate. A later overlapping write still stops recovery, and neither
ownership nor initialization follows from this value equality.

The stronger bridging that crosses `BlockDeclared` and `CellsForgotten` is
scoped to viewability reasoning through `with_extended_dag_bridging`. Enabling
that reasoning globally can change which surface facts a planner selects and
therefore change expansion spellings. Isolated memory-resolution fuel keeps
a nested graph query from consuming the caller's bounded reasoning budget.

The bridging and the explicit certificate check (`with_extended_dag_bridging`,
`explicit_dag_check_active`) are thread-local modes, so a memo whose
computation can read either one keys on both. Otherwise an answer computed
inside the scope would be served outside it, where the bridging must not
apply, or the reverse. The resolution memos, the context-inconsistency memo,
the DAG load-equality memo and the atomic derivation memo each do.

Loop havoc uses the same edge-local rule as call havoc when a whole-loop effect
summary has been checked: its owned ranges are carried on `LoopHavoc`, and a
load may cross with evidence that it is outside every range. A declaring loop
also retains the flat ownership withheld from its body. Explicit read transport
may select one indexed kept range covering the entire read, even if a
conditional collection over-approximates the mutable footprint. The persistent
kept-range identity is part of the havoc marker; states with different
frames cannot intern together. No composite or alias search is enabled.
The copy-back
in `prepare_loop_top_state` materializes entry cells already known to be stable;
it is an abstract-state optimization, not the soundness source for post-loop
load transport. If a footprint cannot be evaluated, the edge retains the
unconditional barrier semantics.

A loop frame may also select a live borrowed-view/owner partition by the
queried footprint and read addresses. `BorrowPartitionRangeEvidence` retains
the selected composition and both members. Its checker requires that exact
authority to remain available, verifies the entire mutable range is contained
by its member, checks both endpoints of the full read, and rejects overlap
under current address equalities. Unbound views and view-only compositions
provide no such frame. Candidate indexes alone grant no separation, read
permission, or native-object validity. The selected-member query avoids walking
unrelated holdings or constructing pairwise separation facts.

## Range index domains

`MemoryRange` retains either signed `Int32` or unsigned `UInt64` bounds.
Its legacy `start()`, `end()` and `byte_footprint()` methods deliberately
reject native ranges. Numeric consumers must dispatch on `int32_bounds()` /
`wide_bounds()`: reading a native bound as a signed residue can frame a
write that actually overlaps a read. Structural traversal uses `bound_terms()`;
rewrites, base alignment and containment keys retain the range's kind.
A narrow equality cannot substitute the whole value of a native bound; native
bound substitution requires a full-width equality.

`pointer_access_in_memory_range` selects the existing access rule for the
range's domain. Native access still requires one whole element, proved
membership and a nonwrapping byte extent. Cross-width or signed-only reasoning
that cannot establish these conditions returns unknown or refuses the proof.
It grants no permission by truncating a bound or weakening the kernel assertion.
Loop effect frames and resource-body readable-memory facts keep native extents. Signed
fold framing, iterated-element selection, allocation coverage and indexed
certificates explicitly decline unsupported native inputs.

The remaining private signed helpers are reached only after their callers'
native dispatch: byte normalization in coverage/splitting/overlap, range-length
and count arithmetic in containment, and the signed ranges constructed by
iterated ownership and C program-entry storage. Their source comments record
those boundaries. `wide_range_reader_tests` cover native bounds above 2³²,
alias alignment, resource unfolding and projection, loop frames, certificates,
missing-resource diagnostics and mixed domains/element widths.

## Bounded two-state load equality

A two-state load equality first uses the typed common-ancestor read walk.
It advances the newer endpoint until the paths meet, retaining each checked
no-write hop, and stops before their shared older history. If an intervening
step affects the read or cannot be framed, the existing source/value walks
still decide stored-value equality, endpoint pinning, or refusal. Transport
traces name the successful stop as a common state. The cold-query scaling
regressions `load_equality_ignores_history_before_both_states` and
`load_equality_work_tracks_the_state_delta` distinguish history before both
states from the steps between them, including a previously written cell.

## Source and tests

The representation and edge producers live in
`src/kernel/primitives/memory_state.rs`. The consumers live primarily in
`src/kernel/reasoning/memory_resolution.rs` and memory-load reasoning. Focused
shape, boundary, sibling-state, marker-preservation, and scaling regressions
live in `src/kernel/tests/memory_dag_tests.rs`; heap lifetime edges also have
coverage in `src/kernel/tests/heap_tests.rs`.

The chronological implementation record, measurements, and rejected
experiments are preserved in `design/memory-dag.md`. They aren't part of the
current architecture contract.

## Failed explicit transport walks

A rejected `transport(source, target) using { ... }` reports the cell walks
actually performed while checking that operation. Each observation identifies
the queried address and byte width, starting and stopping states, number of
crossed edges, stopping reason, and the extended/explicit DAG modes used by the
query. The address and state identities share the checked source, target,
and execution facts' exact formatter and construction legend.

These observations are captured as each walk returns, not reconstructed by
walking memory again while rendering the error. They describe checker queries,
not additional facts or a proposed missing premise. Repeated identical
observations are shown once; memo hits perform no new walk. Capture is scoped
to the explicit check and restored on return or unwind; ordinary memory
queries retain no diagnostic history.
