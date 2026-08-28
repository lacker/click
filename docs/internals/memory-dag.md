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
| `Store` | One pointer was assigned a value. The transition's fact context is frozen on the edge. |
| `LoopHavoc` | A loop may have changed memory without a precise write set. |
| `CallHavoc` | A call may have changed declared mutable ranges. |
| `BlockDeclared` | A new non-havoc block entered the memory model. |
| `CellsForgotten` | Possibly aliasing cached cells were discarded on a write path. |
| `HeapAllocationPending` | An allocation request has an unresolved base and extent but no successful storage yet. |
| `HeapAllocated` | A fresh allocation identity and extent became live. |
| `HeapFreed` | An allocation identity and extent stopped being live. |

Entry states have no parent edge. Failed allocation returns to the existing
pre-allocation identity instead of recording a backward edge.

## Structural invariants

Every recorded parent identifier is smaller than its child identifier. The
parent must therefore exist first and a derivation cycle can't be constructed.
Recording is first-wins: if interning finds an existing equal memory value, it
keeps that node's established provenance.

Derivations are advisory evidence. Missing provenance can make a reasoning
query fail to establish an equality, but it can't make an invalid equality
true. Walks are bounded and fall back to the checked reasoning path
when an edge is missing or can't be crossed safely.

The graph never treats a lifetime boundary or an unknown write as an ordinary
unchanged store. In particular:

- a `Store` edge is crossed only with sufficient pointer-distinctness evidence:
  distinct blocks, a decided common-base offset inequality, or one strict
  order recorded in the edge's frozen context that separates the two
  indexes (an indexed lookup, never a derivation, so the assumption-free
  naming walk can use it);
- a `CallHavoc` edge is crossed only with sufficient range-disjointness evidence;
- a `LoopHavoc` edge isn't crossed as proof that an arbitrary load is unchanged;
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
scoped to loadability reasoning through `with_extended_dag_bridging`. Enabling
that reasoning globally can change which surface facts a planner selects and
therefore change expansion spellings. Isolated memory-resolution fuel keeps
a nested graph query from consuming the caller's bounded reasoning budget.

`CLICK_DISABLE_MEMORY_DAG=1` disables recording and DAG consumers for an A/B
experiment. It is a contributor control, not a supported proof technique; a
correct proof must not rely on toggling it.

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
