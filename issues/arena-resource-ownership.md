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

The next boundary is shared arena metadata. `arena_read` reloads the backing
pointer through `region->arena->data`. The region owns the selected backing
cells but only views the arena's `data` field, so without a stable separation
invariant the verifier must consider the backing element to alias that
pointer-valued field. That alias would make an `int32` read a type mismatch.
This is a real missing contract fact, not a range-containment failure.

Do not add the separation fact as an ad hoc precondition to each accessor.
The next experiment should model stable shared arena identity/metadata once,
so every live region can rely on the same backing-pointer and separation facts
while no region individually owns the shared arena fields. Determine whether
the existing viewed-composite mechanism can express that invariant. If it
cannot, the likely language gap is a general stable shared-resource operation
or a way to name a checked ghost resource argument without first reloading it
through the resource it helps expose. It is not an arena- or range-specific
operation.

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
