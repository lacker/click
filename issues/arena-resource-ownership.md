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

## Next chunk: connect the symbolic region to free and the pipeline

Give `arena_free` a contract over `arena_prefix_region` that returns the
region's occupancy and data cells to the state it came from, and verify
`arena_pipeline` over the symbolic transition. Returning a region that is not
the last one allocated needs a partition with holes, which the prefix model
cannot express; decide that representation against the fixed C before adding
syntax. Keep arbitrary holes out of the first free chunk if the pipeline's
reverse-order frees can be modeled as prefix shrinks.

The first attempt was blocked at contract lowering, before any proof ran.
The fixed `arena_free`, `arena_read`, and `arena_write` take only the region
descriptor, so their contracts must name the arena as `region->arena`, and
the live-region resource owns that descriptor. A field-bearing resource's
folded cells were not read authority for sibling contract clauses, while a
field-free composite's and a decided match arm's were. That gap is closed: an
unconditional, unmatched field-bearing body now publishes the cells it owns
as read authority while a contract's resource clauses are evaluated, and
ownership still moves only on `unfold`
(`mdtests/arena_prefix_free_reads_region_arena.md`,
`mdtests/contract_owns_through_field_bearing_instance.md`). The landed
two-parameter `arena_prefix_region(arena, region)` still cannot be named from
the region alone, because its own argument reads a cell it owns, and resource
fields cannot have a struct pointer type, so the region resource has to take
the region alone and reach the arena as `region->arena`.

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
