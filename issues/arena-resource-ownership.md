# Verify user-defined arena region ownership

## Status

Open. The load-variable naming defect that blocked unfolding the arena's
two-level region shape is fixed and retained as
`mdtests/load_variable_naming_epoch.md`.

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

The symbolic endpoint itself no longer appears to require a language change.
A C scalar carried by a matched algebraic resource payload can select a memory
range, and unfold/fold preserves the symbolic suffix. Resource facts may also
quantify over a bounded subrange of contained memory: definition validation
checks that the quantified interval is covered, and resource rewriting checks
the corresponding universal viewability obligation from the same contained
authority. The positive end-to-end regression is
`mdtests/resource_match_payload_memory_endpoint.md`.

The same experiment fixed one adjacent parser gap. A child introduced by
`let { slot: child } = unfold(parent)` initially has only its parent's provisional
family in parser state; a loop binder may now take over that child under the
family declared by the selected arm, with declaration expansion still checking
the actual slot family. The regression is
`mdtests/loop_binder_takes_over_unfolded_cross_family_child.md`.

Loop-local model destructuring now works through proof conditionals. A proof
`match` on a loop-owned resource model inside `preserve by` keeps its scalar
constructor bindings available while lowering a nested proof `if`; the
surface proof still records the original condition, and its generated
certificate independently verifies. The focused regression is
`mdtests/loop_preserve_if_reads_match_binding.md`.

The matched quantified-fact boundary is now fixed. A proof `match` on the
model field of an exactly named folded resource publishes a flat selected
arm's facts in the kernel-issued constructor partition, including facts that
name a constructor payload. Arms that contain child instances retain the
existing explicit `let { ... } = unfold(parent)` boundary, because matching their
model must not implicitly unfold child ownership. The kernel resolves the one
flat instance by its resource field projection, evaluates the facts against
the arm's own contained memory, and records the exact additions that
independent certificate checking must reproduce; it does not scan ambient resources or
premises. Explicit `instantiate` can use a
bounded universal fact before `unfold`, and an unchanged arm can be unfolded,
updated with a value preserving the fact, reproved, and folded again. The
positive and negative regressions are
`mdtests/resource_match_quantified_fact_round_trip.md` and
`mdtests/resource_match_quantified_fact_rejects_changed_load.md`; expansion of
the positive grouped proof independently reverifies. The reduction also
showed that refolding after an explicit unfold already retained the necessary
load identities: the missing step was publication of binding-dependent arm
facts at proof-match entry, not a separate fold identity mechanism.

The stable-loop-invariant export gap is now fixed. Both direct cursor execution
and forward planning associate declared invariants with the checked statement
transition's producer-owned `introduced_facts` delta, in its original order,
after skipping the rule's effect summaries. They no longer recover that delta
with a suffix guess or membership filtering against ambient facts, so an
already-known invariant retains its checked export position and unrelated
sibling facts cannot enter the mapping. The focused source regression is
`mdtests/loop_stable_invariant_export.md`; its grouped expansion independently
reverifies, and unit coverage checks exact ordering plus output-sized
iteration.

The early-return postcondition lowering gap is now fixed. When lowering a
checked proposition at one exact return outcome produces several candidates,
the kernel selects a candidate only when all of its routing facts are exactly
stated at that outcome and no sibling is also selected. The source proof
keeps that candidate's facts and completed proposition, and whole-function
contract certification repeats the same checked selection before matching the
recorded completion. It never accepts the first candidate, infers a survivor
merely because siblings conflict, or scans unrelated ambient facts. The focused
source regression is
`mdtests/early_return_indexed_postcondition_path_selection.md`;
its grouped expansion independently reverifies. Unit coverage rejects
ambiguous and unrouted alternatives, distinguishes a selected later candidate
from an unproved first candidate, and pins selection work independently of the
ambient fact count.

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

The use-after-free rejection lives in `mdtests/arena_use_after_free.md`. The
live-region resource of the symbolic allocation now has focused negatives too:
`mdtests/arena_prefix_region_double_free.md` refuses a second free of one
region, and `mdtests/arena_prefix_regions_reject_overlap.md` refuses folding
two regions over overlapping intervals.

The adjacent allocation is now parameterized, in
`examples/arena/arena_symbolic_alloc.click`, against the fixed C. The state
resource `arena_prefix_state` carries the occupied prefix and live count as
plain `int32` fields; its `arena_prefix_partition` child selects the free data
suffix `[prefix, capacity)` with the field as the range endpoint. The
partition stays folded through the count-validation branches, is opened for
the scan and mark loops, and is restored at the same prefix on every failure.
Success returns the state at `prefix + count` and `live + 1` plus an
`arena_prefix_region` owning exactly `[prefix, prefix + count)`; only the
success/failure outcome is a `spec enum`. `click verify`, `click expand
--claim`, `click audit`, and `click profile` agree on it.

Three general gaps were fixed on the way, each with its own regression:

- `let { field: name } = unfold(instance)` binds a C-typed field's folded
  value, so loop invariants and refolds can name it after the unfold
  consumed the instance (`mdtests/resource_unfold_binds_scalar_field.md`,
  `mdtests/resource_unfold_binds_children_and_fields.md`,
  `mdtests/resource_unfold_field_binding_rejects_consumed_read.md`).
- Unfolding an unmatched field-bearing body now names its cells as a matched
  arm's are, so a loop that writes through a range the body owns keeps the
  range's base load (`mdtests/resource_unfold_names_unmatched_body_cells.md`).
- A decided C branch inside a loop body now expands to the checked execution
  split it spells, so whole-claim expansion of a preservation proof verifies
  (`mdtests/loop_preserve_decided_branch_expands.md`).

## Prefix free, reads, and writes

`examples/arena/arena_symbolic_alloc.click` now verifies the fixed
`arena_free`, `arena_read`, and `arena_write` over the prefix resources, beside
the symbolic `arena_alloc`. `arena_prefix_region(region)` takes the descriptor
alone and reaches the arena as `region->arena`; resource fields cannot have a
struct pointer type, and the earlier two-parameter form's own argument read a
cell it owns.

- `arena_free` is a prefix shrink: it consumes the most recently allocated
  region (`freed.end == before.prefix`, `1 <= before.live`,
  `before.live - 1 <= freed.start`) and the state, clears `occupied[start..end]`
  through the C loop, refolds the partition at prefix `start`, and produces the
  state at `prefix == old(freed.start)` and `live == old(before.live) - 1` with
  the descriptor.
- `arena_read` and `arena_write` borrow the region and the state, require the
  index inside the region's interval in field terms, keep both instances'
  fields, and state the cell in C terms.

What made these expressible, each with its own regression:

- An unconditional, unmatched field-bearing instance body publishes the cells
  it owns as read authority wherever the contract's own clauses are read: at
  the callee's entry, at its return, in contract certification, and at a call
  (`mdtests/arena_prefix_free_reads_region_arena.md`,
  `mdtests/contract_owns_through_field_bearing_instance.md`,
  `mdtests/contract_returns_field_bearing_sibling.md`,
  `mdtests/contract_postcondition_reads_through_field_bearing_instance.md`,
  `mdtests/call_through_field_bearing_sibling.md`, and the two refusals
  `mdtests/contract_field_bearing_instance_views_grant_no_write.md` and
  `mdtests/contract_field_bearing_instance_views_only_owned_cells.md`).
  Ownership still moves only on `unfold`, and a loop head does not publish.
- Normalization rejoins two held ranges that abut by a proved endpoint
  equality, so the freed interval returns to the free suffix under
  `end == prefix` (`mdtests/fold_joins_ranges_abutting_by_proved_equality.md`,
  `mdtests/fold_join_needs_the_endpoint_equality.md`).
- Surface synthesis no longer spells a cell an array field points to as an
  `int32` index of a struct-pointer local, which had made the clearing loop's
  invariant closer refuse its own bundle.

## Next chunk: the pipeline

`arena_pipeline` remains unverified. A proof against the contracts above was
worked out outside the gate and got this far:

- Initialization converts to the prefix state with checked folds: unfold
  `arena_init_result` and `arena_initialized_access`, unfold and refold
  `arena_initialized_storage` to expose `1 <= capacity <= 536870911`, prove the
  two separations while the backing ranges are visible, fold the partition at
  prefix 0 and the state at `prefix == 0, live == 0`. The storage composite
  stays folded beside the state and is what `arena_empty` needs again.
- Both allocations, their failure branches (the second one freeing `first` as a
  prefix shrink), the writes of 11 and 22, both reads, the value `33`, the
  reverse-order frees, the combined allocation of 4 from prefix 0, and its
  write of `value` all step through the binder maps. Each borrowed call gives
  the region and state fresh fields, so the proof carries them with a `mark`
  before the call and `have x == at(mark, x)` after it; `simp` does not chain
  the call's field equality with an earlier `have` by itself. The value read
  back from the combined region at index 3 did not yet close the same way.
- Converting the final state back to `arena_empty` folds. The
  `arena_destroy` call was refused on every path because the call rule could
  not show that a kept owned descriptor lies outside an allocation the callee
  frees; that kernel gap is closed
  (`mdtests/call_retires_allocation_beside_unrelated_owner.md`,
  `mdtests/arena_destroy_beside_region_descriptors.md`), and the pipeline has
  not been re-run against it since.

Two tooling findings from that work need their own fixes before the pipeline
lands:

- The store in `arena_write` costs about 126,000 deterministic units alone,
  and over 2,000,000 (its smart budget; 500,000 as a simple `step`) when the
  `arena_init` or `arena_destroy` proof is verified earlier in the same
  sidecar. The work is in pointer distinctness over explicit ranges
  ("explicit range: recursive candidates", "range membership: offset
  equality"), so a proof's cost depends on unrelated proofs verified before
  it. Placing `arena_init` and `arena_destroy` after the region functions
  avoids it but only hides it; reduce it first.
- `arena_init`'s quantified postcondition over `occupied` has no caller-side
  spelling, so `instantiate` cannot name it; `simp` proves the restated
  quantifier.

The planned sidecar restructuring (lifecycle resources in a resources-only
file imported by `arena.click` and the pipeline sidecar, with the `arena_init`
and `arena_destroy` proofs moved beside the pipeline) is deferred until the
destroy call is admitted, since only the pipeline needs it and moving the
proofs ahead of the region functions trips the cost blowup above.

## Open design question: frees out of allocation order

The pipeline frees in reverse order, which the prefix model expresses as
shrinks. A free of any other region leaves a hole below the prefix that the
fixed C's first-fit scan may later reuse. Three representations fit the fixed
C differently.

A partition listing live intervals. The state carries a sorted list of live
`[start, end)` intervals as a model and owns the data cells of every gap
between them through a resource recursive over that list; the occupancy map is
related by `occupied[k] == 1` exactly when `k` lies in a listed interval.
Allocation shows the first-fit run found by the scan lies in the first gap
large enough and inserts the interval; free removes one from anywhere and
merges the gaps on either side. It names exactly what the C's regions are, but
it needs list-indexed recursive ownership and list reasoning inside the scan
loop's invariant, which states per-cell facts.

A per-cell occupancy view. The state owns the whole occupancy map and, for
data, exactly the cells whose occupancy is 0: an iterated ownership guarded by
the stable value of a cell the same resource owns. This is closest to the C,
which decides availability per cell and needs no coalescing: allocation moves a
run of free cells to a region while setting them occupied, free moves them back
while clearing them, and the scan invariant stays per cell. It needs a new,
general ownership form (value-guarded iterated ownership) in the kernel.

A prefix plus a free list. Keep the prefix and add a list of holes below it:
freeing the last region shrinks the prefix, freeing any other pushes a hole.
It extends the model that verifies today in the smallest step, but it makes
coalescing an explicit list normalization the C never performs, and relating
first-fit to the earliest hole large enough requires the list to stay sorted
and merged, so the scan proof inherits the partition model's list reasoning
anyway.

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
