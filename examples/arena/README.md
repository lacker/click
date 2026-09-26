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
`arena_reuse` frees the middle one of three regions and allocates the same
size again.

The C is the fixed implementation boundary for the resource-modeling work;
`arena_reuse.c` is the acceptance driver added for the reuse fixture.

## Sidecar layout

A caller can use a callee's contract only when the callee is verified earlier
in the same sidecar, and imports carry resources but not C function specs.

`arena_cells.click` is the arena's only sidecar: the per-cell occupancy
representation, every C function over it (`arena_init`, `arena_alloc`,
`arena_free`, `arena_write`, `arena_read`, `arena_destroy`,
`arena_region_length`), then `arena_pipeline` and `arena_reuse`. It declares
its own resources.

Two earlier models are retired. One held the occupied cells as a prefix
beside a free suffix (`arena_prefix_state`, `arena_prefix_region`). It
verified the pipeline, whose frees in reverse order it expresses as prefix
shrinks, but it could not express a free out of allocation order. The other
verified `arena_alloc` only as the first allocation from an empty arena and
the region functions over one fixed interval. The per-cell model verifies
each of those functions under a more general contract, so neither is the
only coverage of anything. The mdtests written against the earlier resources
(`mdtests/arena_prefix_region_double_free.md`,
`mdtests/arena_prefix_regions_reject_overlap.md`,
`mdtests/arena_destroy_beside_region_descriptors.md`) declare them inline and
stay.

## The per-cell model

`arena_state` owns the arena's four fields, the allocation authority, and an
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
  `[region->start, region->end)` occupied now and free before the call, and
  every other cell unchanged. The scan loop carries its free run in an
  `arena_scan` window, so its per-cell run fact is a resource fact checked at
  each fold; the mark loop owns an `arena_window`, takes each cell's element
  out of the iterated fact, and marks it, which the store rule closes.
  Because nothing ties `live` to the number of regions, the increment's
  definedness is the precondition `st.live < 2147483647`. It also states
  `arena->capacity <= 536870911`, `st.capacity == arena->capacity`, and, on
  success, `0 <= region->start` and `region->start < region->end`.
- `arena_free` consumes any live region and the state, with `1 <= st.live`
  and `r.end <= st.capacity`, clears `[start, end)` through an
  `arena_clear_window` that gives each cell's element back to the iterated
  fact after its flag is cleared, and produces the descriptor and the state
  at `live - 1`, with every cleared cell `0`, every other cell unchanged, and
  `region->arena->capacity` kept.
- `arena_read` and `arena_write` borrow the region and the state, require
  the region to lie inside the arena (`r.end <= st.capacity`), and leave
  every occupancy cell, `region->arena`, and the arena's `capacity` and
  `data` unchanged, with `r.end <= st.capacity` again at return. The cell
  written or read is stated both as `region->arena->data[region->start +
  index]` and as `region->arena->data[r.start + index]`: the field spelling's
  definedness is the precondition's, so a caller that keeps the region
  folded can use it without opening the descriptor. `arena_read`'s result is
  the cell's value before the call, and `arena_region_length` borrows both
  too. The state is named `arena_state(old(region->arena))`: a borrowed
  instance is re-read at the call's return, and the callee owns the
  descriptor (`mdtests/borrowed_instance_argument_reads_old_field.md`).

Both loops that write the map must own all of it, because the iterated
fact's guard cells must be owned by the body that declares it, so each loop
havocs every occupancy cell. What a loop leaves alone is a frame invariant
against the loop's entry, and the contracts' frames chain those to the
function entry (`mdtests/loop_frame_through_folded_state_field_cells.md`,
`mdtests/loop_keeps_cells_the_function_keeps_owning.md`).

## The pipeline

`arena_pipeline` verifies on all five paths: initialization failure, each of
the three allocation failures, and success, which returns `33`
(`ensures result == 0 or result == 33`). Every call lends the folded
`arena_state`, whose iterated clause spans the whole data buffer; the caller
keeps its region descriptors and the other regions' data outside each
transfer, and the call rule keeps a cell an owned member of the caller's
residual resources holds
(`mdtests/call_keeps_region_beside_folded_arena_state.md`).

The proof carries an occupancy invariant: every cell outside the live regions
is free, spelled against the snapshots at which the regions were allocated
(`k < at(z1, first->start) or at(z1, first->end) <= k`). Each allocation
extends it from the callee's per-cell frame, each read and write preserves it
through the callee's clause that every occupancy cell is unchanged, and each
free restores the freed interval through its clause that the cleared cells
are `0`, so the map is all free again before every `arena_destroy`. Region
endpoints are tracked through the regions' fields
(`r1.start == at(z1, first->start)`), and the live count and capacity through
the state's fields, one `have` per carried fact across each call.

The value written through `first` is carried across the write through
`second` with an explicit `transport` whose frame evidence is the kept range
(`mdtests/call_keeps_a_region_cell_read_through_its_descriptor.md`); `simp`
does not find that step. The combined region's index `3` is in range by its
fields: `r3.end == r3.start + 4` follows from the allocation's postcondition
once `defined(r3.start + 4)` is proved on the field, and the cell written and
read back is named through `r3.start`.

Where `simp` was slow or did not close, the proof is written with explicit
steps. Of its 370 `simp` calls, 104 are `simp() using` with their premises
listed, and it states 449 `have`s, 48 `instantiate`s, 17 `rewrite`s,
5 `apply`s and 2 `transport`s. `click expand --claim arena_pipeline.contract`
replaces the remaining smart steps with checked simple ones.

## Reuse after a free out of order

`arena_reuse` frees `middle`, the region `[2, 4)` of a six-cell arena whose
other cells are occupied by live regions on either side, and allocates two
cells again. Its contract proves
`result == 1 implies 2 <= reused->start and reused->end <= 4`: every cell of
the new region is one of the freed cells. The proof shows that after the free
the only free cells are `2` and `3`, and `arena_alloc`'s postcondition that
the allocated cells were free before the call places the new region among
them. With the allocation's length that is the freed interval itself, but the
contract states only the containment: `simp` did not use a definedness fact
proved about the loaded `reused->start` to discharge the guard of the
allocation's `reused->end == reused->start + 2`, as it does for one proved
about a region field in the pipeline, and this fixture does not pin that.

The driver reads `middle->arena` into a local after `arena_free(middle)` has
returned the descriptor, and its contract names the returned state
`arena_state(old(middle->arena))`. Both reasons the local and the `old`
were introduced are now closed: a region can be unfolded while the caller
also owns another descriptor of its type
(`mdtests/unfold_region_beside_an_object_of_its_type.md`), and a descriptor
field the caller holds flat is carried across a later call whether or not
its value is cached
(`mdtests/call_keeps_an_uncached_flat_field_beside_folded_state.md`). The
driver still uses the local and the `old`; rewriting its contract as
`produces after: arena_state(middle->arena)` has not been retried since.

This is the weaker form of first-fit reuse: the freed hole is the only free
run, so any successful allocation of that size lands in it. First fit itself
(the chosen run is the first one of its size) is not stated, because a
resource fact cannot yet read cells under a nested quantifier's guard, which
the scan loop's invariant would need (every earlier window of `count` cells
holds an occupied cell).

## Limits

- Nothing relates `live` to the number of occupied cells or regions (the
  kernel has no count of a guarded population), so `arena_alloc` requires
  `st.live < 2147483647` and `arena_destroy` requires the all-free map
  rather than `live == 0`.
- A call that lends an iterated fact havocs every cell the fact could hold,
  whatever the callee writes; the caller's frame across it comes only from
  the cells it keeps owning.
- `arena_reuse` still copies `middle->arena` into a local and returns the
  state as `arena_state(old(middle->arena))`; both frontiers that forced
  that are closed (above), and the simpler contract has not been retried.

A guarded equality over `int64` terms no longer needs its bounds restated in
the guard's own spelling: `simp` discharges an `int64` sum's or difference's
definedness guard from the bounds in scope
(`mdtests/guarded_postcondition_int64_bounds.md`).
