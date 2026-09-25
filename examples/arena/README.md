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

`arena_pipeline.click` verifies `arena_alloc` as one symbolic
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

## The per-cell model

`arena_cells.click` verifies the same fixed C over the per-cell occupancy
representation, the one that expresses frees in any order. `arena_state`
owns the arena's four fields, the allocation authority, and an
`arena_cells` child: the whole occupancy map plus, through iterated guarded
ownership, exactly the data cells whose occupancy is `0`. Its fields are
`live` and `capacity`; its facts are `0 <= live`, the capacity bound, and
the separations of the arena object and the two backing ranges.
`arena_region` owns the descriptor and exactly `data[start..end]`, with
`region->start == start`, `region->end == end`, and `0 <= start < end`.
Nothing mentions a prefix.

- `arena_init` zeroes the map, forms the iterated fact with `gather`, and
  returns `arena_init_outcome`: the untouched descriptor on failure, the
  state at `live == 0` on success, with every occupancy cell `0`.
- `arena_destroy` requires every occupancy cell `0`, dissolves the fact with
  `scatter`, and frees both allocations. The state cannot count occupied
  cells, so this all-free precondition, not `live == 0`, is what makes the
  free safe.
- `arena_alloc` places the region anywhere: failure returns the state at
  the same `live` and the caller's descriptor, with every occupancy cell
  unchanged; success returns the region with
  `region->end == region->start + count` and
  `region->end <= arena->capacity`, the state at `live + 1`, every cell of
  `[region->start, region->end)` occupied, and every other cell unchanged.
  The scan loop carries its free run in an `arena_scan` window, so its
  per-cell run fact is a resource fact checked at each fold; the mark loop
  owns an `arena_window`, takes each cell's element out of the iterated fact,
  and marks it, which the store rule closes. Because nothing ties `live` to
  the number of regions, the increment's definedness is the precondition
  `st.live < 2147483647`.
- `arena_free` consumes the region and the state, with `1 <= st.live` and
  `r.end <= st.capacity`, clears `[start, end)` through an
  `arena_clear_window` that gives each cell's element back to the iterated
  fact after its flag is cleared, and produces the descriptor and the state
  at `live - 1`, with every cleared cell `0` and every other cell unchanged.
  It needs no prefix: any live region can be freed.
- `arena_read`, `arena_write`, and `arena_region_length` borrow the region
  and the state.

Both loops that write the map must own all of it, because the iterated
fact's guard cells must be owned by the body that declares it, so each loop
havocs every occupancy cell. What a loop leaves alone is a frame invariant
against the loop's entry, `arena->occupied[k] == at(mark_free_run.entry,
arena->occupied[k])` below `start` and from `end` on, and the scan loop
frames the whole map the same way; the contracts' frames chain those to the
function entry. The bundles close with explicit closers: each map member is
transported from the map's viewability stated just before the loop, and the
field `&arena->occupied` the map is read through adds no member
(`mdtests/loop_frame_through_folded_state_field_cells.md`). The clearing loop
reads `region->end` in its condition while its window's iterated clause spans
all of `data`; the descriptor stays with the function, so the loop head keeps
its cells (`mdtests/loop_keeps_cells_the_function_keeps_owning.md`).

What the per-cell sidecar does not yet verify is the pipeline; the prefix
model below keeps verifying it. Every call in the pipeline passes the folded
`arena_state`, and a call havocs the callee's footprint, here the whole data
buffer through the iterated clause. The caller keeps its region descriptors
and the other regions' data outside the transfer, so the callee cannot write
them, and the call rule now keeps a cell an owned member of the caller's
residual resources holds, opening a residual `arena_region` one layer
(`mdtests/call_keeps_caller_object_beside_folded_state.md`,
`mdtests/call_keeps_region_beside_folded_arena_state.md`).

## Sidecar layout

A caller can use a callee's contract only when the callee is verified earlier
in the same sidecar, and imports carry resources but not C function specs. So
the files are split by what they share:

- `arena_resources.click` is a declaration module: the lifecycle resources
  (`arena_initialized_storage`, `arena_initialized_access`,
  `arena_init_result`, `arena_empty`) and the prefix resources
  (`arena_prefix_partition`, `arena_prefix_state`, `arena_prefix_region`),
  and nothing to verify on its own. It names `object(arena)`, whose struct
  layout comes from an importer's `verifying` sources, so it is checked where
  `arena.click` and `arena_pipeline.click` import it; a directory target does
  not select a declaration module as an entry.
- `arena_pipeline.click` proves every contract the pipeline calls:
  `arena_init`, the symbolic `arena_alloc`, the prefix-shrink `arena_free`,
  `arena_write`, `arena_read`, and `arena_destroy`, in that order, then
  `arena_pipeline` itself, and declares `arena_pipeline.c`. It holds the `ArenaPrefixAllocOutcome` enum and
  `arena_prefix_alloc_result`, which only the symbolic allocation uses.
- `arena.click` keeps the fixed-interval model: `arena_metadata`,
  `arena_region`, `arena_available`, the specialized first allocation of
  `arena_alloc`, and `arena_region_length`, `arena_read`, `arena_write`, and
  `arena_free` over `arena_region`.
- `arena_second_alloc.click` stays the fixed instance check of the pipeline's
  second two-cell allocation.
- `arena_cells.click` holds the per-cell model: its resources, the three
  loop windows, `arena_init`, `arena_alloc`, `arena_free`, `arena_write`,
  `arena_read`, `arena_destroy`, and `arena_region_length`. It declares its own resources
  rather than importing `arena_resources.click`, because `arena.click`
  imports that module and already names a different `arena_region`.

## The pipeline

`arena_pipeline` verifies on all five paths: initialization failure, each of
the three allocation failures, and success, which returns `33`
(`ensures result == 0 or result == 33`). Every path ends in
`arena_destroy(arena)` while the caller still owns its region descriptors
(`mdtests/arena_destroy_beside_region_descriptors.md` is that call alone).

- Initialization converts to `arena_prefix_state` at `prefix == 0,
  live == 0` with checked folds: unfold the result, access, and storage,
  refold storage at `1`, prove the two separations, and fold the partition
  and state. Each path back to `arena_destroy` converts the other way with
  `unfold(state)`, `unfold(partition)`,
  `fold(arena_initialized_access(..., 1))`, and `fold(arena_empty(arena))`.
  A theorem cannot transform resources, so these are inline folds on each of
  the four destroy paths.
- Each call's fresh state fields are carried with `mark` before the call and
  `have x == at(mark, x)`, `have at(mark, x) == c`, and a `simp() using` of
  the two after it.
- The allocation's `region->start == old(before.prefix)` has no caller
  spelling; `extract(combined->start == at(a3, s4.prefix))` names it.
  `defined(combined->start + 3)`, which guards the write and read
  postconditions at index 3, needs the descriptor's cells readable: unfold
  the state and then the region, `rewrite` and `normalize`, and refold both.
  The value read back at index 3 is then `33`.

The pipeline frees in reverse order, which the prefix model expresses as
shrinks. Frees out of allocation order are the open representation question
in `issues/arena-resource-ownership.md`.
