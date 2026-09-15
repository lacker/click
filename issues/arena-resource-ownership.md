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
the stable `data`, `occupied`, `capacity`, and `live_regions` fields plus both
backing allocation authorities. Scoped opens borrow that body without
duplicating it, so distinct live regions can share metadata while retaining
exclusive ownership of their own data and occupancy intervals. No new surface
form was needed.

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
bounds, restores the descriptor and shared metadata, and returns both the
cleared occupancy interval and its backing data interval as an
`arena_available` resource. The next bounded blockers are `arena_alloc` and
the end-to-end `arena_pipeline`.

The empty-arena lifecycle now verifies independently of that partition model.
`arena_init` returns an `arena_init_result` plus conditional initialized access:
failure retains the zeroed caller-owned descriptor and no allocation, while
success returns both allocation authorities, both complete backing ranges, and
a checked quantified guarantee that every occupancy cell is zero. Its two
allocation-failure paths release every partially created allocation.
`arena_destroy` consumes `arena_empty`, which combines the successful result
with complete backing access and `live_regions == 0`, frees both allocations,
zeros the descriptor, and returns it. The focused
`mdtests/arena_destroy_with_live_region.md` regression rejects destruction when
the caller holds only a live-region resource.

The use-after-free rejection already lives in
`mdtests/arena_use_after_free.md`. Double free and overlapping live regions
still need focused negative regressions.

## Next chunk: allocator partition

Verify `arena_alloc` as the next bounded experiment. It must transfer exactly
the chosen interval while preserving an arena-owned description of every other
free interval, including holes created by prior allocations and frees. Start
from the verified successful `arena_init` outputs and diagnose the smallest
first-allocation transition before attempting the full pipeline. If the
current language cannot express that transition, reduce the exact boundary to
a focused regression before proposing a general ownership-collection
extension. Keep the C fixed throughout.

## Violated invariant

Click should be able to verify an allocator built in ordinary C from one
backing allocation. Every successful `arena_alloc` must transfer exclusive
read/write authority for exactly the returned region, and `arena_free` must
consume that authority and return its interval to the arena. The allocator
must not require a kernel-built-in notion of an arena allocation.

The existing resource language can package a particular memory interval in a
composite region resource and can share stable arena metadata through a counted
population. It is not yet established whether it can update the arena's
arbitrary partition of occupied and unoccupied cells without a new general
ownership-collection operation. Diagnose that boundary against the fixed
implementation before proposing syntax or semantics.

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

Retain the focused use-after-free and destruction-with-live-region mdtests, and
add negative mdtests for double free and overlapping live regions. Keep
zero-sized allocation as a normal failed allocation, matching the fixed C.

## Acceptance criteria

- All eight arena C functions have checked contracts and proofs, including the
  end-to-end pipeline, and the project verifies under the normal examples gate.
- Allocation and free are expressed as checked transformations of ordinary
  user-declared resources over the primitive backing memory and allocation
  authority.
- Any language extension is general enough to describe ownership collections
  rather than being special-cased to arenas or integer ranges.
- Explicit simple proof steps do work proportional to their named inputs and
  produced resource delta; they do not scan or clone unrelated resources.
- `scripts/check.sh` passes with the positive project and negative mdtests.
