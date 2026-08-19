# Load terms in arithmetic positions make simple checks recursive

## Violated invariant

Simple steps must be fast to analyze, so memory snapshots must be treated
as large objects: owned by the proof context and queried, never carried
into the small terms that checkers compare, normalize, and order. Today a
loaded value can flow into pointer arithmetic as
`Bitvector32Term::MemoryLoad(SharedCMemory, ptr)` inside
`PointerOffsetTerm::Int32Scaled`, e.g. an array cell addressed by a loaded
index (`data[owner->len]`). Every alias or distinctness query over such an
offset must decide arithmetic over a term that names a snapshot, and
deciding it triggers memory resolution, whose alias sub-obligations
compare more load-bearing offsets — a recursion in which a handful of
top-level queries fan out into millions of work units.

Quantified: in `mdtests/field_derived_precise_effect_after_metadata_write.md`,
the strict check of `have owner->data == old(owner->data)` issues only 8
top-level general-alias queries yet consumes ~1.6M deterministic units
(nested attribution: derived separation 3.06M with children,
general-alias range 1.98M, explicit-range inside the bounded memoized
path 1.21M, indexed candidates 0.67M), failing its 2M budget — while the
same-shaped `owner->cap == old(owner->cap)`, whose lowering touches no
array cells, checks in 394 units. The quarantined owned-vector example
stalls on the same mechanism ("giant-term memory-resolution cost", see
`issues/push-contract-path-dropped-by-laundered-inconsistency.md`), so
this issue is the shared root cause behind both.

## What already exists (scoping findings, 2026-08-18)

The architecture half-implements the principle:

- `SharedCMemory` is an arena-interned handle with O(1) equality and
  hashing (identity plus precomputed content hash). Only `Ord` still
  falls back to structural `CMemory` comparison (deliberately, for
  deterministic BTreeMap iteration, because arena ids are not stable
  across replays).
- An atomic-load layer already treats load terms as canonical names:
  `certified_store_equations` emits `load(after, ptr) == value` defining
  equations, `canonicalize_atomic_loads` rewrites loads to canonical
  forms, and the memory-DAG provenance
  (`AtomicMemoryLoadEqualityEvidence`) derives cross-snapshot load
  equalities lazily.

What is broken is therefore not the representation of the snapshot but
its *position*: unresolved load terms participate in arithmetic, so
deciding arithmetic recursively invokes resolution.

## Design

At the boundary where a loaded value enters an arithmetic position
(pointer offsets first; general bitvector contexts as a follow-up), it
must become a small term:

1. resolve the load immediately when resolution is cheap (store
   equations, DAG edge), producing an ordinary term; otherwise
2. mint a fresh verification variable (`next_verification_variable`,
   already replay-deterministic) and record the defining fact
   `var == load(snapshot, ptr)` — the shape `certified_store_equations`
   already produces — so the snapshot stays proof-side and is consulted
   only when the defining fact is used.

The atomic-load layer keeps working: defining facts carry the
`(snapshot, pointer)` pair, so provenance can still connect loads across
snapshots; equation right-hand sides may retain load terms because they
are consulted, not decided over. `Ord`'s structural fallback shrinks to
those retained positions and can move to a canonical snapshot naming
later if it still matters.

Intervention points (census): `PointerOffsetTerm::Int32Scaled`
constructions whose `value` can be an arbitrary term — contract-range
lowering in `src/kernel/spec.rs` (~517), the canonicalization sites in
`src/kernel/memory_provenance.rs` (~158, ~1004–1054), and the kernel
execution paths that compute element addresses from loaded indices (to
be enumerated when implementation starts; the census above lists every
file touching the term).

## Intended regression

- The metadata-write mdtest's `owner->data` have strict-checks within the
  same order of magnitude as its `owner->cap` sibling (hundreds to
  thousands of units, not millions), pinned as a deterministic budget in
  the test.
- A multi-size scaling curve over writes-crossed-per-load showing the
  strict check grows linearly with writes, not with recursion depth.
- Corpus parity over both fixture gates: no proof outcome flips.
- Milestone: the owned-vector quarantine's honest proof becomes
  checkable (its own issue tracks the dropped-path soundness question).

## Acceptance criteria

- No `MemoryLoad` term reachable inside `PointerOffsetTerm` after
  execution lowering; a debug assertion or probe run over the gates
  demonstrates it.
- The regressions above are green, and
  `issues/explicit-have-goal-path-gaps.md`'s dispatch lands without any
  bounded checking mode.
- This file and its Open-list line are deleted when the fix, its
  regressions, and the linked issues' updates land.
