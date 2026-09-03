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
arena metadata. The remaining allocator entry points are still unverified;
`arena_destroy` must also require that no live regions remain.

`arena.click` keeps every source in the C0 parser gate and declares checked
contracts for `arena_region_length`, `arena_read`, `arena_write`, and
`arena_free` over the `arena_region`, `arena_available`, and shared
`arena_metadata` resources. `arena_init`, `arena_alloc`, and `arena_destroy`
remain unverified; the open arena resource-ownership issue defines that proof
work rather than treating the parser-only sources as verification of the
allocator.
