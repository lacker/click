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

## Frontier after the 2026-08-14 master rebase (prototype on 56706c0b)

The rebase absorbed the havoc-marker fix and the honest-proof machinery;
`pool_pipeline`'s `0 <= pool->checked_out` premise (item 1 below) now
replays — the landed bounded matcher and premise bridges were exactly its
prescribed fix. The unit suite passes and the frontier is
`pool_transfer_pipeline.contract` tactic 3: the re-established population
invariant (an `And` theorem premise spelled at the post-`pool_checkout`
snapshot) has no replayable derivation. Traced end to end:

- The premise's conjuncts (e.g. `0 <= load(M_3havocs, dest+0)`) are
  skeleton-identical to ambient facts spelled at the post-`pool_init`
  snapshot; only the memory operand differs. The snapshot bridge fails
  because `c_memory_load_is_unchanged`'s derivation walk cannot connect
  the two spellings.
- Two walk gaps found and fixed on the prototype: (a) the load evaluator
  reduced memories by dropping alias-distinct cells without recording the
  reduction, so walks dead-ended at unrecorded variants — it now records
  the existing `CellsForgotten` edge; (b) the replay and the independent
  kernel certification build *parallel derivation chains* for one
  execution, so the target is a sibling spelling, never the same interned
  object — the walk now tests each hop against the target with the
  bounded pointer-load matcher (havoc marker sets must agree), and the
  intra-arena id-ordering early exit is gone because it only bounds
  object reachability, not sibling matching.
- With both fixes the walk descends the full replay chain, crossing the
  source-range havocs (verified against the recorded mutable ranges —
  dest-range havocs and the dest store are correctly refused). The one
  remaining gap: at the marker-equal hop the two spellings differ by a
  single cell **at the loaded pointer itself** — a materialization cell
  valued `load(pristine, dest+0)` on the walk side, absent on the target
  side — and the bounded matcher refuses a differing cell at the loaded
  pointer. Whether that cell is a legitimate materialization (transparent
  by definition) or a stale spelling minted before `pool_init(dest)`'s
  store must be answered by inspecting its minting site before the
  matcher learns to see through it; a wrong answer here would launder the
  init store.

## Deeper trace: the premise state is wrong before the bridge runs (2026-08-14 late)

Chain-dumping the failing tactic's `CStatementVerifies` state settled where
the mismatch is minted, and it is upstream of every bridge:

- The replay state presented for `pool_transfer_pipeline`'s transfer
  statement has a memory whose own content asserts
  `destination->checked_out = load(entry, destination->checked_out)` — a
  pristine materialization cell that survived `pool_init(destination)`.
  The recorded footprints are all correct (traced: every `pool_init`
  evaluation at a one-marker entry records `v100001` ranges; canonical
  footprint recording changes nothing, `changed=false` on every range),
  so the wrong cell is not a footprint or canonicalization bug: the
  replay-side state construction for the second call kept a cell the
  call's havoc should have dropped. Where that state is built is the next
  question; `851fde96`'s "stored resolved forms when pairs were present"
  is the suspect family.
- Because the laundered content is alpha-identical to
  `pool_pipeline`'s honest post-`return` state (same fresh-variable and
  marker numbering across function verifications, and the object arg
  really is untouched there), the content-addressed arena interns them as
  one node, and first-wins derivation recording gives it
  `pool_pipeline`'s three source-ranged edges. Memory terms are
  self-contained, so the foreign edges are still true *of the content* —
  the conflation is not itself unsound, but it makes diagnosis
  treacherous and it means an alpha-collision can hand a wrong replay
  state a plausible-looking history. A regression should pin that two
  functions with alpha-identical states cannot exchange derivations in a
  way that changes any verdict.
- The two DAG-walk gaps fixed this session (unrecorded `CellsForgotten`
  reductions; sibling-chain matching with the bounded matcher, replacing
  the intra-arena id-ordering early exit) are correct and stay, but they
  cannot close the frontier while the replay state itself is laundered.

## Remaining to close, in order

1. The examples fixture gate. The 500,000-unit budget exhaustion is
   **fixed** (prototype `c6644a83`): the cost was per-query depth, not
   repetition — three snapshot comparisons of four differing cells each
   ran the composition-backed general alias search per cell, from the
   small-snapshot pre-pass in `c_memory_load_is_unchanged` (which ran
   before the bounded DAG walk) and from the effect-summary
   endpoint-matching closures inside a prop-facts candidate scan. Both
   now use a bounded-alias comparison (memoized resolution check +
   assumption-free constant-offset intervals + a materialization-aware
   case for a cell at the loaded pointer), and the full comparison runs
   after the DAG walk for all snapshot sizes, so nothing provable is
   lost. `pool_pipeline` drops from 6.2s budget-death to 39ms; unit
   suite 964/964. Measured and eliminated along the way: memoizing
   `pointers_proven_disjoint_by_range` by (fact-set fingerprint, pointer
   pair) changed nothing — the queries are not identical repeats.

   What remains is functional: the second `open`'s `step() using`
   premise `0 <= pool->checked_out` does not replay. Premise-scoped
   tracing (a thread-local flag set around exactly the failing
   `snapshot_bridge_proves` call, with per-branch logging inside
   `memory_loads_proven_equal`) isolated the one load-bearing failure:

   - The failing bridge has six candidates, all normalized to the
     pristine spelling `load(empty-memory, p)`; the required side is
     `load(M_current, p)` with materialized cross-object cells. For
     every candidate, every branch fails: no transport, resolution
     returns `None` on **both** sides, pointers equal, no syntactic
     match, DAG walk false, snapshot comparison false (block sets
     differ: pristine `{}` against three havoc markers).
   - Resolution's `None` is not a prover gap: with the carriers, the
     bounded distinctness classification of every other cell succeeds
     (zero unclassified-cell traces). It returns `None` because the
     prototype's `M_current` has **no materialized cell at
     `checked_out`** and external memory is not concretely loadable.
     On master the same comparator wins through `resolve` — master's
     memory carries a materialized cell at the pointer, minted earlier
     in execution when the executor could resolve the load with pairs
     (exactly `851fde96`'s "stored resolved forms when pairs were
     present").
   - The DAG walk can never serve this query as spelled: the pristine
     candidate memory is a canonicalization artifact, not an ancestor
     snapshot, so no derivation path reaches it.

   The mint hunt closed the question, and the earlier framing was wrong
   in one respect: master does not serve this premise by resolution
   either. Claim-scoped tracing at the `step() using` premise check
   (`pool_pipeline.contract` tactic 6) shows:

   - On master the premise matches an available fact **byte-exactly**
     (fact and premise both spell 1,056 characters, identical) — the
     `unfold(valid_pool)` fact and the premise lowering coincide. On
     the prototype the same fact spells 1,325 characters: its memory
     operand retains a materialization cell for `first` (value
     `load(pristine, first)`) that the premise's memory holds as
     `Constant(11)` post-store, so exact matching fails and the bridge
     must decide the pair.
   - Inside the failing bridge, the carriers do their job completely:
     **every differing cell is proven distinct from the loaded pointer**
     (`distinct=true` for `first` and `second` against `pool`). The
     comparison never uses those answers, because the candidate's
     normalized memory is fully pristine (`blocks=[]`, `cells=0` — the
     assumption-free canonicalizer strips materialization-valued cells
     and, with them, all havoc markers) while the required side keeps
     three havoc markers and two concrete-valued cells, and
     `memories_match_for_pointer_load_under_assumptions` **rejects on
     its block-set equality prefilter** before the per-cell loop runs.
   - The carriers are present in the bridge's assumption context (the
     `CResourceComposition` propositions ride `all_pure_facts`), so
     this is not a carrier-propagation gap.

   So the whole functional failure reduces to: exact-match identity of
   recorded facts and lowered premises depends on the materialized-cell
   content of their memory operands, which the pairs-vs-carriers switch
   perturbs in both directions; and the bridge that should absorb the
   difference is vetoed by a syntactic block-set filter whose job
   (havoc markers must not be laundered) is legitimate but whose
   placement is coarser than needed. The candidate fix, which is the
   canonicalization design applied here: an assumption-backed canonical
   form for load atoms at fact recording and premise lowering — strip
   cells the bounded provers show distinct from the loaded pointer,
   which collapses both sides to the same spelling whenever their
   difference is materialization noise. The havoc-marker soundness
   question (the pristine canonical form conflates havoc history; the
   existing exact-match transport already relies on this being benign
   between havoc-free points, per the `with_block` soundness-trap
   comment) must be settled in that design before implementation —
   understand why byte-exact matching of pristine-canonical spellings
   across the unfold-to-step gap is sound on master today, and give the
   assumption-backed form the same boundary.
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
