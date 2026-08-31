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
The intended Click proof will give each live region exclusive access to its
backing interval, make `arena_free` consume that authority, and require every
region to be returned before `arena_destroy` can consume the arena.

`arena.click` currently keeps every source in the C0 parser gate but does not
yet declare contracts. This is intentionally a C-only checkpoint; the open
arena resource-ownership issue defines the proof work rather than treating the
parser-only sidecar as verification of the allocator.
