# Memory derivation DAG

Click interns kernel memory snapshots and records how each new snapshot was
derived. The resulting directed acyclic graph (DAG) lets memory reasoning
relate loads across stores, calls, allocation, and other state changes without
reconstructing the complete history from snapshot values.

This is an internal representation. It doesn't add Surface Click syntax or
change which C programs Click accepts.

## Representation

`SharedCMemory` is the stable identity of an interned `CMemory` value. The
arena assigns dense identifiers. A separately stored `CMemoryDerivation`
describes the edge from an already-interned parent to a child snapshot.
Keeping provenance outside `CMemory` means that equality, hashing, and ordering
continue to describe memory values rather than the route used to produce them.

Each map and set inside a snapshot (`blocks`, `cells`, `union_cells`, the
ended-lifetime set, and every heap collection) is a `SnapshotMap` or
`SnapshotSet` from `src/kernel/primitives/persistent_map.rs`: a persistent
B-tree (`imbl::OrdMap` / `imbl::OrdSet`) that also carries a cached content
hash, the wrapping sum of one fixed-key hash per entry. A snapshot therefore
shares structure with the snapshot it came from: cloning a map is O(1), a
store copies only the O(log n) path it changes, and hashing a snapshot reads
the cached sums instead of visiting its cells. The sum is independent of
insertion order, so equal contents hash equally however they were built.
Equality rejects on the snapshot's O(1) content hash, accepts maps that share
a root, and otherwise compares elementwise, charging each compared entry to
the deterministic work counters. Ordering stays lexicographic over entries.

A rule applied at one address visits only the entries that can alias it.
Every snapshot collection is keyed by a `Pointer` (or a key that orders by
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
Loop havoc and the interface join stay whole-memory: their write set is every
reachable cell.

Interning looks up the caller's storage roots first, then the content. A
structural hit registers the caller's roots too, and the arena pins them so
the addresses cannot be reused by other content; asking again for the same
snapshot is then a pointer-identity hit with no comparison.

Execution carries the arena's canonical storage forward. A producer interns
its input as the edge's base and continues from the base's stored instance
(`intern_derivation_base`), and `record_c_memory_derivation` replaces the
result with the stored instance of its content, an O(1) handle clone, so
every snapshot a path carries, and every fact, term, or certified store built
from it, is the instance the arena holds. Equal snapshots therefore share
their roots, and facts that embed them compare by root identity rather than
entry by entry; the recorded edges are unchanged. Because every result is
derived from its base's canonical storage, a statement executed twice from
one state (planned, then checked) is recognized as the base's recorded child
before any structural lookup: the arena indexes each base's recorded children
by content hash, and `CMemory::eq_relative_to` compares the two results'
changes from the base (`SnapshotMap::eq_relative_to`, which diffs against the
base and so walks only the changed paths). The answer is exact whatever the
snapshots share; only the cost depends on the sharing.

The arena is per thread and per verification. Interning dedups by content and
keeps the first derivation recorded for an id, so two verifications sharing
one arena would let the second inherit the first's edges for any snapshot
with the same content — a call havoc of a same-named callee, for example,
since havoc identities restart per verification. `VerificationSession`
(`src/kernel/mod.rs`), entered at the outermost verification boundary,
starts a fresh arena under a new token and empties every table keyed by
arena ids or holding arena snapshots (the load registry, the canonical-form
caches, the reasoning memos, and the per-verification execution caches).
Snapshots from an earlier session still compare by content but answer no
derivation query.

The producers in `src/kernel/primitives/memory_state.rs` record these edge
kinds:

| Edge | Meaning |
| --- | --- |
| `Store` | One pointer was assigned a value. No fact context is recorded on the edge. |
| `LoopHavoc` | A loop may have changed memory; verified whole-loop effects carry a checked write set. |
| `CallHavoc` | A call may have changed the callee's owned ranges, and none of the memory its caller kept owning. |
| `BlockDeclared` | A new non-havoc block entered the memory model. |
| `CellsForgotten` | Possibly aliasing cached cells were discarded on a write path, or cells the loaded pointer is separate from were discarded on a read path. |
| `HeapAllocationPending` | An allocation request has an unresolved base and extent but no successful storage yet. |
| `HeapAllocated` | A fresh allocation identity and extent became live. |
| `HeapFreed` | An allocation identity and extent stopped being live. |

Entry states have no parent edge. Failed allocation returns to the existing
pre-allocation identity instead of recording a backward edge.

## What a snapshot's identity is

A snapshot is its known cells plus the snapshot it was forgotten from.

Interning by content is what lets one node stand for every execution that
reaches it, and a load reads its name from the snapshot it happens at. Both
rely on the content deciding the state. Known cells alone don't: dropping a
cached value leaves the memory unchanged and the knowledge of it gone, and a
cell map that has forgotten a store looks exactly like the cell map before
that store. After `a[i] = 7; a[j] = 0;` the second write drops the possibly
aliasing `a[i]` cell and the map is empty again, as it was at function entry.

So `CMemory` carries a `forgotten_from` mark: the interned identity of the
snapshot cached values were dropped from, part of equality, hashing, ordering
and the interning key. A snapshot means "the memory the mark denotes, with
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

A load's name is not usually this snapshot's hash, because
`load_variable_for_cell_with_origin` first asks the resource tracker for the
cell's epoch — the last program point at which this cell holds the same value
— and names the load there. A cell whose epoch the tracker can reach keeps the
name it had; the mark decides the name only where the walk stops. It decides
the *history* everywhere, which is the point.

A cell the snapshot holds materialized is named by its value before any walk.
An integer cell holding a load variable resolves to that variable through the
canonical form. A pointer cell whose value is exactly the pointer a typed load
of that cell produces (the cell's own block, offset `v * width` at the value's
pointee width, `v` registered as a load of the same address) is named `v`.
That is what keeps a struct field such as `arena->occupied` one name across a
loop head: the walk is assumption-free and stops at the head's havoc, while
the head's copy-back has already kept the cell's value because the checked
footprint is disjoint from it.

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
ancestor and here is one of those stores. `record_c_memory_derivation` counts
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
  common-base offset inequality. No assumptions are captured on the edge,
  because first-wins interning lets paths with different assumptions share
  one edge, and one path's `length == 0` must not preserve another path's
  load;
- a `CallHavoc` edge is crossed only with sufficient range-disjointness
  evidence, likewise checked in the querying context, or when a range the
  caller kept owning outside the transfer holds the cell. Those ranges, and
  the facts of the residual instances they were opened from, are the edge's
  own, and the write-set marker spells them, so every path that shares the
  edge kept the same memory; placing the cell inside one is still decided
  in the querying context;
- a `LoopHavoc` edge with no checked footprint isn't crossed; a verified
  footprint is crossed only with range-disjointness evidence;
- allocation and free preserve unrelated locations but don't preserve a load
  through the affected allocation;
- havoc marker blocks remain attached during materialization-source
  canonicalization, so materialized sibling cells can't hide a havoc.

These rules are soundness boundaries, not search heuristics.

## Consumers and scope

Memory-load equality and unchanged-load reasoning use derivation ancestry to
find a common source snapshot for a specific pointer. A query stops at an edge
whose safety condition it can't prove. Positive answers are cached by stable
snapshot and pointer identities; failed answers can be retried after new
derivation information becomes available.

The stronger bridging that crosses `BlockDeclared` and `CellsForgotten` is
scoped to viewability reasoning through `with_extended_dag_bridging`. Enabling
that reasoning globally can change which surface facts a planner selects and
therefore change expansion spellings. Isolated memory-resolution fuel keeps
a nested graph query from consuming the caller's bounded reasoning budget.

Loop havoc uses the same edge-local rule as call havoc when a whole-loop effect
summary has been checked: its owned ranges are carried on `LoopHavoc`, and a
load may cross only with evidence that it is outside every range. The copy-back
in `prepare_loop_top_state` materializes entry cells already known to be stable;
it is an abstract-state optimization, not the soundness source for post-loop
load transport. If a footprint cannot be evaluated, the edge retains the
unconditional barrier semantics.

## Source and tests

The representation and edge producers live in
`src/kernel/primitives/memory_state.rs`. The consumers live primarily in
`src/kernel/reasoning/memory_resolution.rs` and memory-load reasoning. Focused
shape, boundary, sibling-snapshot, marker-preservation, and scaling regressions
live in `src/kernel/tests/memory_dag_tests.rs`; heap lifetime edges also have
coverage in `src/kernel/tests/heap_tests.rs`.

The chronological implementation record, measurements, and rejected
experiments are preserved in `design/memory-dag.md`. They aren't part of the
current architecture contract.
