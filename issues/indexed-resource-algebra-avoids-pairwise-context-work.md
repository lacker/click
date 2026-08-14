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

## Required design (decided 2026-08-14)

The pairs' accidental effectiveness came from re-stating each separation
fact in every term vocabulary that ever existed, so syntactic lookup never
had to prove cross-snapshot term equality. Re-storing facts per vocabulary
is rejected (it is the original blowup at lower degree). The decided design
attacks the term identity problem directly:

**The underlying theory.** Snapshot-crossing term equality is a
*conditional* rewrite system — `load(havoc(M, R), q) = load(M, q)` only
under `disjoint(R, q)`, and likewise read-over-write — not a set of ground
equalities. Deciding equality in such a system is search, and the
memo/fuel/depth machinery around memory resolution is the cost of serving
that search from inside cheap-looking query paths. The fix is to make a
precise, bounded canonical form exist and to create terms in it, so fact
lookup returns to syntax.

1. **Stratified derivation edges (termination invariant).** A snapshot's
   derivation edge must be described entirely in its *parent's* vocabulary:
   `havoc(M, R)` may spell `R` only with terms grounded at `M` or earlier,
   and stores likewise. Reading `prepare`/footprint lowering shows the
   call-havoc recording already satisfies this — the mutable clause is
   evaluated at the pre-call state (`functions.rs`, "verified call mutable
   footprint lowering") — so this is an invariant to assert, not a bug to
   fix. An earlier revision of this section wrongly claimed the recording
   was self-referential; the traced queries' spellings mention the
   *previous* call's havoc (the legitimate parent vocabulary), not their
   own.
2. **Canonicalize at term creation (bounded guards).** Orient all rewrites
   toward older snapshots. A term is *canonical* iff no oriented rule
   applies whose guard is decidable by bounded indexed lookup — and the
   guard set must include **ground equality facts**, not only frame rules.
   The traced gap is exactly a ground-equality lowering: `buffer_push`'s
   ranges are parent-spelled as `load(M_after_init, owner+8)`, a field
   `buffer_init` wrote, so lowering to the function-entry vocabulary
   (where the composition witness lives) is `buffer_init`'s recorded
   ensures equality `owner->data == data`, not a frame proof. The executor
   canonicalizes terms when it creates them — in particular the mutable
   ranges at footprint lowering — which is the one moment the relevant
   equalities are fresh; cost is DAG height times an indexed lookup. Facts
   then enter the `PureFactContext` already canonical, stored once.
3. **Explicit `rewrite` is the completeness escape hatch.** Equalities
   invisible to bounded guards are stated as proof steps, not chased by
   search. Search completeness remains a non-goal.

Long-run trajectory (for the efficiency guide at close-out, not this
change): the memo/fuel resolution layer is a hand-rolled approximation of
proof-producing congruence closure. If snapshot-equality issues keep
recurring after canonicalization and systematic term interning, the
principled replacement is a forkable, provenance-carrying e-graph fed by
executor-discharged guard equalities — never by guard search.

Two consumers are already converted and verified on the prototype:
post-store certificate transport
(`expanded_read_step_keeps_named_range_separation_premises`) and the
modular-call snapshot path
(`modular_call_snapshot_anchor_replays_with_owned_resource`).

## Monotonicity blocker exposed by symbolic quantities

The symbolic declared-resource quantity prototype exposed a second concrete
consumer on 2026-08-14. The unchanged `examples/bounded-pool` pipeline passes
on master with four historical `CResourceComposition` facts. Replacing the
owned-resource coefficient representation with a symbolic term causes one
additional valid composition fact to survive at the second object store. The
explicit premise `0 <= pool->checked_out` then stops replaying across the
preceding store snapshot even though the same six explicit separation facts,
the same sixteen execution-effect facts, and the same candidate condition
facts remain available.

The failure is not a quantity-arithmetic obligation. After zero populations
were excluded from body activation and transition guarantees were made
proof-producing, the contexts differed only in compact composition history:

- master: four compositions, with fact counts `3, 3, 5, 7`;
- prototype: five compositions, with fact counts `3, 3, 5, 5, 6`.

With normal memoization, `pool_pipeline.contract` tactic 6 (`step() using` at
statement 4) returns a false-negative exact-premise diagnostic. With
`CLICK_DISABLE_DECIDE_MEMO=1`, the same simple store consumes more than
500,000 deterministic work units and trips the simple-tactic gate. Timings on
the normal failure attribute about 40,568 work units to that step, including
repeated `range disjointness: derived separation` queries at about 6,193 work
and `snapshot comparison: general alias` queries at about 6,637 work each.

This pins an additional required property of the canonicalization design:
adding a valid compact composition carrier must be monotone for an already
provable snapshot equality, and a simple exact-premise check must not fall
back to context-wide repeated range derivation. Add a focused regression that
constructs the store/snapshot premise with four carriers, proves it, adds a
fifth unrelated valid carrier, and proves it again with bounded near-constant
work. The symbolic-quantity feature remains blocked until that regression and
the unchanged bounded-pool project both pass.

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

## Canonicalization progress (2026-08-14, prototype `a97036e6`)

The first slice is landed on the prototype and non-regressing (963/964):
`PureFactContext::canonical_bitvector` (bounded ground-equality class walk
with structural simplification joining members), `canonical_memory_range`,
and canonical recording of verified-call mutable footprints. Post-call
cell retention across `buffer_push`-shaped calls now succeeds without
pair propositions — previously every non-local cell dropped, which was
the executor-resolution gap commit `851fde96` predicted.

Two hard-won rules, measured not theorized:

- **Adopt a representative only when it strictly lowers the term** (fewer
  memory loads, or a constant for a non-constant). An unrestricted
  preference respelled loads through alternate snapshots and broke four
  tests whose consumers re-derive recorded ranges and match them
  structurally (`frontier_local_loop_frames_untouched_...` shows the
  failure shape: "effect summary range ... is outside the mutable
  footprint").
- **Piecemeal canonicalization at extra sites moves mismatches around**:
  canonicalizing resource-spec segment evaluation and adding a canonical
  fallback inside `bitvector_terms_proven_equal_for_memory_resolution`
  regressed the same tests without greening the target; both are
  reverted. Creation-site coverage has to move outward in verified,
  test-gated steps.

## Frontier test green (2026-08-14, prototype `f0e1497b`)

Chain matching is resolved. Instrumenting the chain search itself (not
the per-cell comparison) found the divergence at depth 1 in one line:
the desired lineage's final memory ends in a **Store edge over the call
havoc** — proof replay materializes a symbolic load into a concrete cell
by storing the loaded value back — while independent certification never
mints such an edge, so the arm match failed (`call-havoc` vs `store`)
and the store-chain fallback had zero certified stores to work with. A
store whose value is the base memory's own load at the stored pointer
(checked by interned identity, no proving) is a no-op, and derivation
matching now sees through it like the other transparent edges.

With that, `execute_until_expands_vector_storage_call_postconditions`
passes and the **full unit suite is 964/964 on the prototype** for the
first time.

## Remaining to close, in order

1. The examples fixture gate: `bounded-pool`'s `pool_pipeline.contract`
   `step()` at statement 4 exhausts its 500,000-unit simple budget under
   the prototype (also at the pre-canonicalization prototype base, so
   none of the landed slices caused it). This is the same failure the
   monotonicity blocker below records from the symbolic-quantities side.
   Attribution: ~370k units in `snapshot comparison: general alias` →
   `general alias: range`, with `range disjointness: derived separation`
   at ~247k and `indexed candidate`/`indexed facts` at ~184k each.
   Measured and eliminated: memoizing
   `pointers_proven_disjoint_by_range` by (fact-set fingerprint, pointer
   pair) changed nothing — the queries are not identical repeats (the
   fact set evolves between them); the cost is ~40 individually
   expensive queries (~6k units each), so the fix must reduce per-query
   work or stop the exact-premise replay path from running general-alias
   comparison per cell at all.
2. A red deterministic curve: N symbolic same-block owned ranges through
   `observable_facts_assuming_valid` must emit no `CResourceSeparate`
   propositions and near-linear work (red on master today, green on the
   prototype).
3. Full gate on the merged prototype; the unit suite is green (964/964)
   and the mdtests fixture gate needs a completed run once bounded-pool
   passes.
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
