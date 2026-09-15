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
bounds, restores the descriptor and shared metadata, returns both the cleared
occupancy interval and its backing data interval as an `arena_available`
resource, and exposes the exact decrement of `live_regions`.

The smallest first-allocation transition now verifies with existing resource
machinery and the fixed C. `arena_alloc` consumes an all-zero `arena_empty` and
the caller-owned descriptor. Invalid counts return failure with both resources
intact. Success necessarily selects `[0, count)`, transfers that exact prefix
as the live allocation, retains `[count, capacity)` as arena-owned backing and
occupancy ranges, initializes the descriptor, and increments `live_regions`
to one. The result is intentionally specialized as
`arena_first_alloc_result`; it is not a claim that arbitrary holes are already
modeled.

The success resource is flat rather than nesting `arena_region` beside a
suffix resource. A composite resource's opaque sibling cannot supply the
`region->end` load needed to form the other sibling's argument while the body
is being checked. Flattening the same exclusive prefix and suffix authorities
is sufficient for this first transition, so this is a composition constraint
to account for rather than evidence for an arena-built-in operation.

The pipeline's second adjacent allocation now also verifies against the fixed
C, in `examples/arena/arena_second_alloc.click`. The bounded input state owns
the complete occupancy map and free data suffix `[2, capacity)`, leaving the
first live data prefix `[0, 2)` framed in the caller. Failure restores that
state and the caller-owned descriptor. Success transfers `[2, 4)` into the new
region, retains `[4, capacity)`, and increments `live_regions` from one to two.
This establishes that two adjacent live data regions can be held disjointly;
it does not yet make the transition symbolic.

The attempted symbolic form identified a narrower language boundary. The
prior endpoint is not named by an `arena_alloc` C parameter. A resource field
can retain it as model data, but such a field is rejected as the endpoint of
an `owns` range because memory endpoints must currently be C expressions.
Adding the endpoint as a free resource argument does not bind it at the C
contract boundary, and nesting the first region beside a suffix still hits the
opaque-sibling load constraint above. The focused
`mdtests/resource_field_memory_endpoint_rejected.md` regression records the
first and most direct limitation.

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

## Next chunk: symbolic prefix/suffix boundaries

Generalize memory-range selection so a stable scalar stored in a resource can
serve as an owned range endpoint. Start from the focused negative regression
above and add a positive resource-only regression showing that unfold/fold
preserves a symbolic suffix without scanning or cloning unrelated resources.
The mechanism must be general to memory resources; do not special-case arenas
or integer backing arrays.

Then use that capability to replace the two pipeline-specific allocator
contracts with one transition parameterized by the retained prefix endpoint.
It must preserve the caller's live prefix on failure and transfer exactly the
next adjacent interval on success. Keep arbitrary hole collections, freeing,
recombination, and the end-to-end pipeline out of this chunk.

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
