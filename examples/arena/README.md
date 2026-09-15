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
The intended Click proof gives each live region exclusive access to its
backing interval. `arena_free` now consumes that authority, clears the
occupancy map through a checked loop, and returns both the backing and
occupancy intervals as an `arena_available` resource together with the shared
arena metadata. Allocation remains the unresolved ownership-partition
transition.

`arena_init` and `arena_destroy` now verify as an independent empty-arena
lifecycle. Initialization returns the caller-owned descriptor on every path,
returns both complete backing allocations and ranges only on success, proves
that every occupancy cell is zero, and releases the data allocation if the
second allocation fails. Destruction requires an `arena_empty` resource with
`live_regions == 0`, consumes both allocation authorities, and returns the
zeroed descriptor.

`arena.click` keeps every source in the C0 parser gate and declares checked
contracts for `arena_init`, `arena_region_length`, `arena_read`, `arena_write`,
`arena_free`, and `arena_destroy` over the lifecycle, `arena_region`,
`arena_available`, and shared `arena_metadata` resources. `arena_alloc` and
`arena_pipeline` remain unverified; the open arena resource-ownership issue
defines that proof work rather than treating parser coverage as verification
of the allocator.
