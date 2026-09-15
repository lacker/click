# Arena

This synthetic C0 project implements a first-fit arena over a runtime-sized
`int32` allocation. An `arena` owns the backing storage and a parallel
occupancy map. A `region` identifies one live half-open interval `[start, end)`
inside that storage.

`arena_alloc` finds the first contiguous unoccupied interval of the requested
positive size, marks it occupied, and initializes a caller-supplied region
descriptor. `arena_free` releases that interval. Because availability is
represented per cell, freeing adjacent regions automatically makes their
combined interval available to a later larger allocation; no separate
coalescing operation is required.

The pipeline allocates two adjacent regions, reads and writes through both,
frees them in reverse order, and then allocates one region spanning their
combined space. It cleans up correctly along every allocation-failure path.

The C is the fixed implementation boundary for the resource-modeling work.
The Click proof gives each live region exclusive access to its backing
interval. `arena_free` consumes that authority, clears the occupancy map
through a checked loop, and returns both the backing and occupancy intervals
as an `arena_available` resource together with the shared arena metadata. Its
contract also exposes the exact decrement of `live_regions`.

`arena_alloc` now verifies for the first allocation from a freshly initialized
empty arena. Invalid counts return failure without consuming the empty arena
or the caller-owned descriptor. A successful allocation transfers the exact
prefix `[0, count)` into `arena_first_allocation` and retains the adjacent
suffix `[count, capacity)` in the same outcome resource. This deliberately
specialized contract establishes the first ownership-partition transition
without pretending that arbitrary holes are modeled yet.

`arena_second_alloc.click` verifies the pipeline's next allocation as a
separate, equally explicit transition. Its input state describes the occupied
prefix `[0, 2)` and owns the free data suffix `[2, capacity)` plus the complete
occupancy map. The first live region can therefore remain framed in the
caller. Failure restores that state and the caller-owned descriptor; success
returns the new region `[2, 4)` and retains `[4, capacity)` for the arena. The
contract is intentionally fixed to the pipeline's two-cell allocations: the
prior endpoint is not a C parameter, and a resource field cannot currently be
used as a memory-range endpoint.

`arena_init` and `arena_destroy` now verify as an independent empty-arena
lifecycle. Initialization returns the caller-owned descriptor on every path,
returns both complete backing allocations and ranges only on success, proves
that every occupancy cell is zero, and releases the data allocation if the
second allocation fails. Destruction requires an `arena_empty` resource with
`live_regions == 0`, consumes both allocation authorities, and returns the
zeroed descriptor.

`arena.click` keeps every source in the C0 parser gate and declares checked
contracts for `arena_init`, the specialized first-allocation form of
`arena_alloc`, `arena_region_length`, `arena_read`, `arena_write`, `arena_free`,
and `arena_destroy` over the lifecycle, `arena_region`, `arena_available`, and
shared `arena_metadata` resources. The second specialized `arena_alloc`
contract lives in `arena_second_alloc.click`. `arena_pipeline` remains
unverified. The next ownership experiment is to make a resource-stored scalar
usable as a stable memory-range endpoint, then replace these fixed boundaries
with one symbolic prefix/suffix transition. Arbitrary free-interval
collections remain later work.
