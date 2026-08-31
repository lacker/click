# Verify user-defined arena region ownership

## Status

The fixed C0 implementation lives in `examples/arena/`. Its parser-only
sidecar deliberately contains no contracts yet. Do not change the C merely to
make the proof easier; it is the source boundary for this project.

## Violated invariant

Click should be able to verify an allocator built in ordinary C from one
backing allocation. Every successful `arena_alloc` must transfer exclusive
read/write authority for exactly the returned region, and `arena_free` must
consume that authority and return its interval to the arena. The allocator
must not require a kernel-built-in notion of an arena allocation.

The existing resource language can package a particular memory interval in a
composite region resource. It is not yet established whether it can represent
and update the arena's arbitrary partition of occupied and unoccupied cells
without a new general ownership-predicate operation. Diagnose that boundary
against the fixed implementation before proposing syntax or semantics.

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
