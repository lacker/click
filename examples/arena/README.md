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

`arena_symbolic_alloc.click` verifies `arena_alloc` as one symbolic
transition over a retained prefix. Its `arena_prefix_state` resource carries
two plain fields, the occupied prefix `prefix` and the live count `live`, and
owns the arena metadata plus an `arena_prefix_partition` child: the complete
occupancy map, the free data suffix `[prefix, capacity)`, and the facts that
every occupancy cell below `prefix` is 1 and every one from `prefix` on is 0.
The field selects the endpoint of the owned suffix directly; no algebraic
model or `match` is involved. For a symbolic `count`, invalid counts and a
scan that finds no run of `count` free cells return failure with the state at
the same fields and the caller-owned descriptor. Success returns the state at
`prefix + count` and `live + 1` together with an `arena_prefix_region` that
owns the descriptor and exactly `[prefix, prefix + count)`, and the contract
states `region->start == old(before.prefix)`, `region->end == region->start +
count`, and `arena->live_regions == old(before.live) + 1`. Only the
success/failure outcome keeps a `spec enum`. The proof names the fields where
it unfolds the state, `let { partition: partition, prefix: p, live: n } =
unfold(before);`, so the scan loop's invariant, the mark loop, the transported
occupancy facts, and every refold can say `p` and `n` after the state itself
is consumed.

The same sidecar verifies the fixed `arena_free`, `arena_read`, and
`arena_write` over those resources. `arena_prefix_region` takes the region
descriptor alone and reaches the arena as `region->arena`, so each contract can
name both resources from the region argument: while a contract's clauses are
read, the folded region publishes the cells its body owns as read authority
for its siblings. `arena_free` is a prefix shrink. It consumes the most
recently allocated region (`freed.end == before.prefix`) together with the
state, requires `1 <= before.live` and `before.live - 1 <= freed.start`, clears
`occupied[start..end]` through the C loop, refolds the partition at prefix
`start` by rejoining the freed data interval to the free suffix under
`end == prefix`, and produces the state at `prefix == old(freed.start)` and
`live == old(before.live) - 1` together with the descriptor. `arena_read` and
`arena_write` borrow the region and the state, require the index inside the
region's interval in field terms, keep both instances' fields, and state the
value read or written as `region->arena->data[region->start + index]`. The
`arena.click` read, write, and free contracts are over `arena_region` and the
shared `arena_metadata` population instead, which the prefix model does not
use, so they stay as the fixed-interval forms.

`arena_second_alloc.click` verifies the pipeline's second allocation as a
separate, fixed transition. Its input state describes the occupied prefix
`[0, 2)`, owns the free data suffix `[2, capacity)` plus the complete
occupancy map, and states the occupancy facts as requirements. Failure
restores that state and the caller-owned descriptor; success returns the new
region `[2, 4)` and retains `[4, capacity)` for the arena. Its resources are
not the symbolic ones, so it is not literally an instance of the symbolic
contract; it stays as the fixed instance check of the pipeline's second
two-cell allocation.

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
shared `arena_metadata` resources. The fixed second allocation lives in
`arena_second_alloc.click` and the symbolic prefix transitions in
`arena_symbolic_alloc.click`.

`arena_pipeline` remains unverified. Its every path ends in
`arena_destroy(arena)` while the caller still owns its region descriptors, and
the call rule cannot yet show that a descriptor the caller keeps lies outside
an allocation the callee frees
(`mdtests/call_retires_allocation_beside_unrelated_owner_frontier.md`). The
rest of the pipeline's shape has been exercised against these contracts
outside the gate; `issues/arena-resource-ownership.md` records how far it got
and the open representation question for frees out of allocation order.
