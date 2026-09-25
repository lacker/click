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
`examples/arena/arena_pipeline.click` (formerly `arena_symbolic_alloc.click`), against the fixed C. The state
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

`examples/arena/arena_pipeline.click` (formerly `arena_symbolic_alloc.click`) now verifies the fixed
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

## The pipeline

`arena_pipeline` now verifies in the examples gate, on all five paths
(initialization failure, each allocation failure, and success returning
`33`), in `examples/arena/arena_pipeline.click` after the callee proofs it
uses. `examples/arena/README.md` describes the proof: inline conversions
between `arena_initialized_access`/`arena_empty` and `arena_prefix_state`
on each path, `mark` and `at` to carry each call's fresh state fields, and
`extract` to name the new region's start. The resources-only module is back
beside its importers as `examples/arena/arena_resources.click`: a directory
target no longer selects a declaration module (imports, types, predicates,
pure functions, and resources only) as an entry.

Landing it needed the kernel to stop growing with the pipeline's owned
objects and accumulated facts, which all sit in the one `ExternalArgument`
block:

- Composition validity compares an owned range only with the ranges a fact
  could relate it to (same base root, an exact alias, or a recorded-equality
  class of the root's index term), and asks the explicit-separation veto
  only after the endpoints prove an overlap. Validity refuses a proven
  overlap, so an overlap nothing states needs no work
  (`composing_a_parameter_object_ignores_unrelated_parameters`,
  `validity_of_parameter_objects_is_linear`,
  `parameter_validity_still_refuses_related_overlaps`).
- A held composition no longer projects its `N(N-1)/2` same-block pairs into
  every fact context; separation queries ask its owned members once each
  (`holding_a_parameter_composition_states_no_pairs`,
  `one_parameter_separation_query_is_linear_in_the_owned_objects`).
- `has_condition_fact`, the ordering modulo canonical load atoms, and the
  symbolic pointer-equality hop read condition facts by key instead of
  scanning them (`condition_fact_queries_ignore_unrelated_facts`).
- The smart `simp` equality-rewrite loops observe their tactic's deadline
  and work budget (`equality_rewrite_search_observes_the_deadline`).

The unit took 36.6 s (the pipeline 33.8 s, 6.6 s of it smart) and missed the
30 s project limit; it now takes about 11 s with no smart tactic near its
budget. Most of what remains is proof-aware pointer equality between
parameter fields (`range membership: offset equality`, `explicit range:
recursive candidates`), linear per query in the owned members of the block.

Acceptance re-audit: all eight C functions, including the pipeline, have
checked contracts and proofs and verify under the examples gate; allocation
and free are checked transformations of user-declared resources; no
arena-specific language extension was added; the intended-regression
behaviors are covered by the pipeline's paths and the negative mdtests
(`arena_use_after_free.md`, `arena_destroy_with_live_region.md`,
`arena_prefix_region_double_free.md`, `arena_prefix_regions_reject_overlap.md`).
The remaining open item is the representation question below, which the
reverse-order pipeline does not exercise; the per-cell section after it
records how far the chosen representation has come.

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

## The per-cell model

The per-cell occupancy representation was chosen and the kernel has it as
iterated guarded ownership. `examples/arena/arena_cells.click` verifies the
fixed `arena_init`, `arena_alloc`, `arena_write`, `arena_read`,
`arena_destroy`, and `arena_region_length` over it: `arena_state` owns the
fields, the allocation authority, and an `arena_cells` child holding the map
and the data cells whose occupancy is `0`; `arena_region` owns the
descriptor and `data[start..end]`. Initialization forms the iterated fact
with `gather`, destruction requires an all-free map and dissolves it with
`scatter`, and allocation places the region anywhere, with the scan's run
held in a loop window and the mark loop taking each element out of the fact
before marking it. `examples/arena/README.md` has the contracts. The
allocation contract states nothing about occupancy cells. `click expand`
now re-verifies a guarded quantified postcondition closed after execution
(`mdtests/guarded_quantified_postcondition_expands.md`), so expansion no
longer blocks them; the proofs do. The failure frame does not close after
the scan loop, which owns and havocs the whole map with no frame invariant
(the loop-frame frontier below), and the success path's closing `simp`
exhausts its smart budget on the marked run, which needs an explicit proof
from the mark window's post-loop fact.

Three kernel defects were fixed on the way, each with a regression:

- A loop binder or a callee's resource-derived frame that holds a
  field-bearing instance or an iterated fact was summarized as writing none
  of its memory, so `transport` carried a stale value across a loop or call
  that wrote the cell. This was a soundness bug: both regressions prove a
  false postcondition on the earlier kernel
  (`mdtests/loop_binder_instance_footprint_includes_its_memory.md`,
  `mdtests/call_through_instance_footprint_includes_its_memory.md`). The
  footprint now opens an instance one layer and spans an iterated fact. An
  instance that cannot be opened from one state (an undecided matched arm, a
  recursive body) and a recursive composite still contribute nothing; that
  gap is open.
- `gather` over a freshly allocated, loop-zeroed map read the guard cell as
  an uninitialized heap cell before consulting the quantified fact
  (`mdtests/iterated_ownership_gather_fresh_heap_map.md`).
- Iterated-fact invalidation walked the recorded history of a content-equal
  snapshot instead of the transition's own, and dropped the fact in a loop
  whose branch resets a local (`mdtests/iterated_ownership_survives_branch_reset.md`).

The loop-frame frontier is closed. The mark loop's bundle used to carry
viewability members for the pointer field cell `&arena->occupied`, which an
unfolded `arena_state` holds as the word carrying its load: spec lowering
asked for the cell's viewability because the word is narrower than the
pointer, while the C evaluator reads it with no premise. It now reads it the
same way, so the field adds no member
(`mdtests/loop_frame_through_folded_state_field_cells.md`, the two-hop twin,
and a negative that rewrites the field). A loop written in a proof now reads
`old(...)` at the checked function entry, a written `both` over a bundle
spells each member alone, and a folded instance publishes the cells of its
field-free composite children, so certification reads `arena->occupied[k]`
inside `arena_state`. The clearing loop's window spans all of `data` through
its iterated clause, which covered the region descriptor the C condition
reads; a declaring loop now keeps the cells the function keeps owning,
because its body can only view them
(`mdtests/loop_keeps_cells_the_function_keeps_owning.md`).

`arena_alloc` now states its occupancy: failure leaves every cell unchanged,
success marks `[region->start, region->end)` and leaves every other cell
unchanged. `arena_free` is verified with no prefix: it consumes any live
region with the state, clears its cells, gives each data cell back to the
iterated fact, and returns the state at `live - 1` with the cleared cells `0`
and every other cell unchanged. What is still open is the per-cell pipeline
and the frees out of allocation order it exists for; the prefix sidecars stay
until it verifies.

The call rule that blocked the pipeline is fixed: a call havoc keeps a cell
an owned member of the caller's residual resources holds, opening a residual
field-bearing instance one body layer, so the pipeline's region descriptors
and the other regions' data survive a call that lends the folded
`arena_state` (`mdtests/call_keeps_caller_object_beside_folded_state.md`,
`mdtests/call_keeps_region_beside_folded_arena_state.md`, with the flat
control `mdtests/call_keeps_caller_object_beside_flat_ranges.md`). The
first-fit acceptance fixture waits on the per-cell pipeline. First fit itself is not
stated either: the scan would need an existential invariant (every earlier
window of `count` cells contains an occupied cell); without it a caller can
still show a same-size allocation reuses a freed middle region when the hole
is the only free run, through the frames.

The per-cell pipeline draft now reaches the first read. What moved it:
`simp` uses a comparison a definedness guard holds under
(`mdtests/guarded_postcondition_closes_after_call.md`; the `int64` form is
`mdtests/guarded_postcondition_int64_bounds_frontier.md`), chains the
equalities a scope's `have`s state and rewrites through loaded pointer
fields (`mdtests/simp_chains_equalities_stated_in_a_scope.md`,
`mdtests/rewrite_through_a_loaded_pointer_field.md`); `arena_read` and
`arena_write` state their occupancy, capacity, and data frames and name the
state `arena_state(old(region->arena))`
(`mdtests/borrowed_instance_argument_reads_old_field.md`); and two search
costs the draft exposed are gone (a failing `simp` case-split nested over
every call outcome in scope, and each quantified-frame instantiation
rewriting whole memory snapshots). It verifies initialization failure, both
destroys after a failed allocation, the second allocation's
zero-outside-both-regions invariant, both writes with that invariant
carried across them, and the call of the first read. The next frontier is
the value that read returns, `first`'s written value carried across
`arena_write(second, ..)`: every link of the
pointer-field chain proves, but `simp` does not compose it
(`mdtests/pointer_field_alias_chain_across_call_frontier.md`). The prefix
sidecars stay until the pipeline verifies.

Two further limits of the per-cell contracts: nothing relates `live` to the
number of occupied cells or regions (the kernel has no count of a guarded
population), so `arena_alloc` requires `st.live < 2147483647` and
`arena_destroy` requires the all-free map rather than `live == 0`; and
first-fit is not stated, because a resource fact cannot yet read cells under
a nested quantifier's guard.

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
