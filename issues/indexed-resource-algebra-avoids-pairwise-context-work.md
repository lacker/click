# Resource contexts materialize and rescan pairwise relationships

`ResourceContext` operations must not enumerate unrelated resource pairs.
The original violations — quadratic validity checks, eager cross-family
separation pairs, linear exact consumption, restart-based normalization —
are fixed, indexed, and curve-gated. What remains is one test kept red by
deleting the last eager pair emission (symbolic same-block memory
separations); the diverging query is now named and traced (see below), and
what is left is a design choice about how the compact carriers serve it.

## Current state

Start from the local branch `claude/lazy-separation-prototype-rebased`
(rebased onto the fmt-gated master; commits through `0fd3c7e5` — several
agents commit daily, so rebase again first). It deletes same-block pair
emission and serves `memory_separation_candidates` from an incrementally
maintained index projected from the compact `CResourceComposition`
carriers — entries identical to the former pair propositions, never
materialized into ambient proposition sets. This is the issue's required
design ("materialize an explicit proposition only when a certificate asks
for it").

Under that prototype, the full default suite passes except one test
(963/964 with `--no-fail-fast`):

```sh
cargo test --lib -- execute_until_expands_vector_storage_call_postconditions
```

## The diverging query, traced

The 2026-08-14 trace (env-gated eprintln instrumentation on both branches,
diffing master against the prototype on this one test) established:

- The failure fires in `certify_c_function_execution_path_resource_representation`
  for `buffer_pipeline`: `values_equal` holds on both branches, but the
  **memory gate** (`c_memories_definitionally_equal` /
  `memories_equal_by_execution_provenance`) fails without pairs. The
  resource gate is never reached; the "missing nonempty_buffer" resource
  delta in the error message is downstream shadow, as already suspected.
- The first failing cell is `owner->cap` (`owner+4`): the desired replay
  materializes it while the certified path leaves a symbolic load across
  `buffer_push`'s `CallHavoc` snapshot. Proving that load unchanged walks
  the havoc edge and asks
  `Assumptions::range_proven_disjoint_from_pointer(mutable_range, field_pointer)`
  where the recorded mutable range is `owner->data[len..len+1]` **spelled
  with loads from the havoc memory itself** and the pointer is an `owner`
  struct field (`+0`/`+4`/`+8`).
- On master, that query family (33 instances in this test) is answered by
  the deep branch of
  `memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution`
  backed by `CResourceSeparate` pair propositions. Crucially, the pair
  scan sees pairs in **several spellings at once**: the entry-spelled
  `separate(object(owner), data[0..cap])` plus mixed pairs whose data side
  is spelled with the same havoc loads as the query. The mixed spellings
  come from the planning replay's post-call `unfold(buffer_storage)`
  (`unfold_composite_resource` → `assumptions_from_propositions`), which
  re-emits observable facts at current spellings. A same-spelling pair
  side lets the scan match shallowly, which breaks what is otherwise a
  bridging cycle: containing the havoc-spelled range in the entry-spelled
  `data[0..cap]` needs `owner->data` unchanged across the same havoc,
  which re-asks the same separation family for `owner+8`.
- On the prototype, the carriers do accumulate at the execution-time sites
  (two compositions present, one havoc-spelled), but the queries still
  fail there, and at the certifier only the entry-spelled carrier is
  present. Direct probing at the failing certifier queries shows deep
  containment of the havoc-spelled range in the entry-spelled carrier
  entry is false even with the reentrancy guard lifted and outside the
  memory-resolution fuel: the base-pointer bridging
  (`load(havoc, owner+8) == data`) is itself the part that master's
  same-spelling pairs made unnecessary.
- Two parity gaps were fixed on the prototype (commit `0fd3c7e5`,
  non-regressing but insufficient): the composition query guard is now a
  bounded depth counter instead of a binary lock that forced every nested
  proof-aware query false, and `range_proven_disjoint_from_pointer` now
  consults the composition's pointer projection at all.

## The remaining design question

The pairs' effectiveness came from existing in one spelling per emission
point — shallow matching then answers snapshot-crossing queries without
recursive bridging. The compact carrier currently reaches each assumption
set in at most one spelling. Two candidate designs, not yet decided:

- (a) Match queries against carrier entries per spelling the way the pair
  scan did: ensure the carrier emitted by each context rebuild (the
  post-call unfold, and whatever populates the certifier's premises)
  reaches the same assumption sets the pairs reached, and compare why the
  execution-time queries fail even with the havoc-spelled carrier present
  — the shallow-match relation over carrier entries may be narrower than
  the pair scan's four orientations.
- (b) Record `CallHavoc` mutable ranges at call time in caller spellings
  (entry spellings here), so the disjointness queries never need the
  self-referential havoc spelling bridged at all. This changes recorded
  derivations, so expansion/replay parity needs checking.

Two consumers are already converted and verified on the prototype:
post-store certificate transport
(`expanded_read_step_keeps_named_range_separation_premises`) and the
modular-call snapshot path
(`modular_call_snapshot_anchor_replays_with_owned_resource`).

## Measured and eliminated — do not re-walk

- An earlier note here claimed the representation certifier never engages
  with pairs; the 2026-08-14 trace disproved that — it engages and all
  three gates pass on master. What stands is that adding proof-aware
  composition fallbacks to the pointer and range disjointness variants
  changed nothing for this test (the pointer one did convert the
  owned-string consumer and is landed; the range one is on the prototype).
- The memory-cell mismatch ("memory snapshots differ", materialized
  call-havoc cells, effect-summary endpoint matching) is downstream shadow
  of the resource divergence, not cause.
- Candidate multiplicity, bucket sizes, and prover fallthrough in the lazy
  index are all measured fine; an earlier lazy-rebuild variant of the index
  was too slow and the incremental maintenance replaced it.
- A budget exhaustion in `box_pipeline` was a separate pre-existing cost
  (certificate construction's ambient rewrite harvest), fixed on master;
  see `atomic-derivation-returns-premises-not-steps.md`.

## Remaining to close, in order

1. Decide between designs (a) and (b) above and make the red test green on
   the prototype without re-materializing pair propositions.
2. A red deterministic curve: N symbolic same-block owned ranges through
   `observable_facts_assuming_valid` must emit no `CResourceSeparate`
   propositions and near-linear work (red on master today, green on the
   prototype).
3. Full gate on the merged prototype; the three frontier tests are the
   sensitive ones, but the fixture gates never ran to completion under the
   prototype.
4. Close-out per `README.md`: durable design into the efficiency guide's
   lazy-separation material, delete this file, and update the burndown —
   which then records zero demonstrated asymptotic violations.

## Landed and gated (for reference)

Exact/family/shape/block/endpoint indexes on `ResourceContext`; ordered
interval validation and insertion; concrete-range and distinct-block
separation without pairs; token/composite pairs removed via the compact
carrier; incremental memory-separation and loadability indexes on
`Assumptions`; indexed non-exact satisfaction and definitional consumption;
checked-execution rebasing at the contract boundary. Curves:
`unrelated_resource_normalization_has_linear_deterministic_work`,
`adjacent_memory_normalization_has_linearithmic_deterministic_work`,
`disjoint_concrete_range_validity_scales_near_linearly`, the
fixed-candidate lookup/consumption regressions, and
`compact_composition_projects_symbolic_separation_without_pair_facts`.
Rejected designs that must not return: a vector-backed loadability bucket
(changed smart-search order), exact-only core deduplication (left stale
views usable after frees), an opaque composition that hid evidence from
condition contradiction, and unrestricted recursive-resource equivalence
probes (measured at 9.5 seconds).
