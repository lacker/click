# Verify user-defined arena region ownership

## Status

The fixed C0 implementation lives in `examples/arena/`; do not change it
merely to make the proof easier. The sidecar now defines an `arena_region`
composite resource and verifies `arena_region_length` through a scoped open.
This establishes that a region descriptor plus its selected backing interval
is expressible without a built-in arena resource.

The first indexed-read experiment also exposed and fixed an independent proof
certificate bug: applications of
`int32_add_nonnegative_right_is_at_least_left` and
`int32_increment_upper_bound` were accepted locally but their kernel
derivations were not retained for whole-function certification. The focused
regression is `mdtests/region_relative_index_read.md`.

Shared arena metadata and `arena_read` now verify with existing machinery.
Each `arena_region` contains one `arena_metadata(region->arena)` unit. Units
with the same arena argument form one counted population whose shared body owns
the stable `data` and `capacity` fields plus the backing allocation authority.
Scoped opens borrow that body without duplicating it, so distinct live regions
can share metadata while retaining exclusive ownership of their own backing
intervals. No new surface form was needed.

The read experiment exposed a kernel alias-resolution bug. A bounded equality
query could retain a speculative alias guard before its nested separation
search reached the compact resource-composition fact. The fast materialized
cell lookup then accepted that equality even when a top-level separation query
proved the cells distinct, producing a spurious `type mismatch`. The lookup
now checks the cached equality candidate against compact-composition
separation before accepting the cell. `arena_read` is the end-to-end
regression; a focused kernel test covers dependent indexed ranges in compact
resource compositions.

`arena_write` now verifies with a one-cell mutable footprint through the
same scoped opens as `arena_read`; the hidden second whole-function
execution that used to fail to reproduce its resource path is gone (the
proof object's typed execution evidence is retained instead; see
`docs/internals/proof-objects.md`). The footprint evaluation had to learn to
name a load through a folded contained unit symbolically. `arena_free` now
consumes the live region, clears its occupancy interval with checked loop
bounds, restores the descriptor and shared metadata, and returns the cleared
interval as an `arena_available` resource. The next bounded blockers are
`arena_alloc`, `arena_init`, and `arena_destroy`.

## Violated invariant

Click should be able to verify an allocator built in ordinary C from one
backing allocation. Every successful `arena_alloc` must transfer exclusive
read/write authority for exactly the returned region, and `arena_free` must
consume that authority and return its interval to the arena. The allocator
must not require a kernel-built-in notion of an arena allocation.

The existing resource language can package a particular memory interval in a
composite region resource. It is not yet established whether it can represent
stable shared arena metadata or update the arena's arbitrary partition of
occupied and unoccupied cells without a new general ownership-predicate
operation. Diagnose each boundary against the fixed implementation before
proposing syntax or semantics.

## Intended regression

Give `examples/arena/arena.click` checked contracts and proofs for the existing
C sources. The pipeline must establish all of the following:

- two adjacent successful allocations own disjoint backing intervals;
- reads and writes are authorized only through a live region resource;
- freeing the regions in reverse order consumes those resources;
- the two adjacent free intervals can be reused by one larger allocation;
- allocation failure preserves the arena and caller-owned descriptor;
- double free and use after free fail because the region resource is absent;
- arena destruction succeeds only after every live region has been returned;
- initialization failure releases any partially created backing allocation.

Add focused negative mdtests for double free, use after free, overlapping live
regions, and destruction with a live region. Keep zero-sized allocation as a
normal failed allocation, matching the fixed C.

## Acceptance criteria

- The arena project has no parser-only qualification and verifies under the
  normal examples gate.
- Allocation and free are expressed as checked transformations of ordinary
  user-declared resources over the primitive backing memory and allocation
  authority.
- Any language extension is general enough to describe ownership collections
  rather than being special-cased to arenas or integer ranges.
- Explicit simple proof steps do work proportional to their named inputs and
  produced resource delta; they do not scan or clone unrelated resources.
- `scripts/check.sh` passes with the positive project and negative mdtests.
