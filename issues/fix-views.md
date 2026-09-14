# P1: Give views stable borrowing semantics

**Status (2026-09-13): the V0-V17 implementation is integrated on master
behind an internal candidate selector. Ordinary contracts still use the
legacy weak-view behavior. Eight steps remain: finish the top-level
borrowed-input root and the rest of the V18 implementation, get the
candidate corpus green, review it adversarially, land escaping borrows,
and cut over. Nothing in this issue is authorization to start agents;
the remaining cards are future assignments.**

This file is the design and the implementation brief. It is organized as:

- [Current state](#current-state): what is on master, how the candidate
  path is selected, and what is parked.
- [Remaining work](#remaining-work): the eight remaining steps, with the
  parked experiment and failure classes they start from.
- [Design](#decision-and-violated-invariant): the decision, the laws, the
  kernel/surface design D1-D14, and the regression catalogue R01-R32.
- [Implementation record](#implementation-record): what each landed card
  established, by commit subject.
- [Working agreements](#working-agreements): assignment, handoff, staging,
  and gate rules for the remaining cards.
- [Concurrency and Rust design checks](#concurrency-and-rust-design-checks),
  [acceptance criteria](#intended-regressions-and-acceptance-criteria), and
  [coordination](#coordination) with neighboring issues.

The dated per-card checkpoint narratives that this file carried while the
cards were in flight are in the git history of this file before commit
"Reorganize the fix-views issue around its remaining work"; the durable
content from them is folded into the implementation record below.

## Current state

**On master.** The candidate stable-view engine exists end to end:

- `src/kernel/loans.rs` is the loan ledger: fresh arena/scope/loan/
  participant/share identities, persistent AVL snapshots, a binary access
  share tree, close and recovery rights, escrow for memory and token pieces,
  checked composite decomposition into primitive loans with an atomic
  restoration group, shared child reborrows, concrete interval indexes for
  active memory loans, and opaque transition evidence bound to the exact
  predecessor state. `src/kernel/tests/loan_model_tests.rs` is the
  independent executable model (two contexts, partition/transfer, shared and
  model-only exclusive reborrows, returned-field transport, mutex guard,
  thread-local confinement).
- `CState` carries the ledger, participant, and occurrence bindings. Direct,
  verified, named, callback, refinement, certification, and proof paths
  route through the joint call-resource planner in `src/kernel/functions.rs`
  and recover only the scopes a call created. Stores, free, realloc, loop
  havoc, and branch abstraction consult the active-loan footprint; unknown
  symbolic overlap fails closed.
- Definition validation and proof-time fold/unfold/observe let a stable view
  cover a resource fact and capture the exact loan dependency. Refusals carry
  a structured category, operation, bounded subject, and origin. Proof and
  cache artifacts are bound to a resource-semantics identity, so a legacy
  result cannot certify a candidate claim. Eight four-size scaling curves
  live in the `src/kernel/loans.rs` tests; the surface scaling suite has no
  loan curve yet (F10).
- The V13 fixtures `stable_view_ordinary_reader`, `stable_view_nested_reader`,
  `stable_view_partial_borrow`, `stable_view_fact_workflow`, and
  `stable_view_returned_pointer` exercise the candidate route through surface
  verification. The reviewed V17 contract migrations and the corpus
  inventory are in
  [`docs/internals/view-output-inventory.md`](../docs/internals/view-output-inventory.md)
  (198 files, 336 explicit `views` declarations). No C source changed.

**Selector.** `ViewSemanticsMode` in `src/surface/verification.rs` has the
variants `Legacy` (default) and `StableLoans`. Candidate fixtures opt in
through `with_candidate_stable_view_semantics`; the mode is part of every
artifact identity. `CLICK_VIEW_SEMANTICS=stable-loans` makes the mdtest and
example harnesses verify every fixture under `StableLoans` through
`verify_c0_sources_in_mode`; the ordinary gate stays `Legacy`. The switch is
rollout scaffolding and is removed in step 8. The earlier codex corpus
counts came from an uncommitted local change and are superseded by the
baseline under remaining work.

**Not on master.**

- The codex V18 experiment, which the borrowed-input root (step 1) was
  re-derived from, is parked as one unverified commit on branch
  `claude/fix-views-v18-wip`. Nothing of it remains to land; steps 1-3
  re-derived or superseded every idea it contained. Take ideas and tests
  from it; do not integrate it as is.

**Borrowed-input root (step 1, landed 2026-09-13).** Under `StableLoans`, a
top-level `views` clause installs a `BorrowedContractInput` loan for the
exact principal resource occurrence the clause selects: no escrow, no close
right, no recovery right, reads and nested reborrows only. Derived
projections and ambiguous equal occurrences are refused at entry. Because a
parameter pointer has a symbolic offset in the shared external block, the
concrete dyadic index cannot hold such a view; the ledger keeps symbolic
protected ranges in a per-block map, bounded by the active loans with
symbolic footprints, and a write, free, or havoc query consults only its own
block's entries. The polarity of that check is deliberate and matches the
rest of the resource algebra: symbolic ranges are separate unless proven to
overlap, compared bytewise. A write reaches the ledger only with owned
authority for its range, and every caller must establish its owned and
viewed inputs as a partition before a call, so an owner-authorized write in
the body is separate from a contract input view by the same contract meaning
that keeps two owners separate; the ledger refuses the writes no partition
can license (through the viewed pointer, through a pointer proven equal to
it, or into a concretely overlapping offset of the same object). A symbolic
query is refused outright while any concrete loan is indexed.

## Remaining work

Eight steps, numbered stably; steps 1-5 landed on 2026-09-13; 6, 7, and 8
remain. Steps 1-5 recover and finish the V18 implementation from the parked
experiment; step 6 is the V18 adversarial review (6.1, 6.2, and 6.3
landed); step 7 is escaping borrows (landed 2026-09-14); step 8 is the V19
cutover, whose pre-check list is in the 6.3 record. Each step follows the working agreements
below: an isolated worktree from master, focused positive and negative tests,
the unfiltered gate, and a handoff. No C source edits, and no change to
`Legacy` behavior before step 8.

Measure every step against the candidate corpus:

    CLICK_VIEW_SEMANTICS=stable-loans cargo nextest run --test mdtests --test examples --no-fail-fast --test-threads 1 --no-capture

Baseline on 2026-09-13 at the commit that added the switch: 187 of 1,509
mdtests and 19 of 26 example projects fail. By error:

- 112 mdtests and 18 examples: "no checked execution matched the contract's
  execution mode", the missing borrowed-input root (step 1).
- 32 mdtests: "inline calls are unsupported with candidate stable-view
  semantics" (step 2).
- 31 mdtests and 1 example: "the required loan backing or binding is
  missing" during planning or access (steps 1-3).
- 2 negatives, `c_callback_contracts_folded_conjunction_deferred` and
  `c_step_contract_one_call_only`, pass under `StableLoans`; understand
  them in step 3, do not re-expect them.
- The composite refusals (steps 4 and 5) do not appear yet because the
  affected fixtures fail earlier at the root.

After step 1 (2026-09-13): 105 of 1,509 mdtests and 15 of 26 examples fail.
The missing-root class is gone. By error: 22 mdtests at "inline calls are
unsupported" (step 2); 12 mdtests and 1 example at "the required loan
backing or binding is missing" (steps 2-3); 6 mdtests and 7 examples at
"this resource shape is outside stable-view support" during entry, which is
a composite or instance input view whose one-level frontier the root refuses
(steps 4-5); 4 mdtests and 1 example at "could not prove the requested ranges
separate"; 4 mdtests and 3 examples at "composite body facts are unsupported"
(step 5); 8 negatives now fail with a different message and the same 2
negatives pass (step 3).

After step 2 (2026-09-13): 45 of 1,509 mdtests and 15 of 26 examples fail.
The inline-call class and the local-array and read-only table views are
gone. What is left is composite and instance input views at entry (6
mdtests, 7 examples), composite body facts (4 mdtests, 3 examples),
unproved range separation (4 mdtests, 1 example), returned-view provenance
and stale evidence on named-contract and callback paths (about 6), expected
negative diagnostics, and a few certification mismatches.

After step 3 (2026-09-13): 23 of 1,509 mdtests and 15 of 26 examples fail.
Apart from the three deliberately unchanged expectations listed under step
3, every remaining failure is a composite or instance class for steps 4
and 5.
After 4a and 5 (2026-09-13): 20 of 1,512 mdtests and 9 of 27 examples
fail; the six buffer examples and four fact fixtures verify. What is left
is step 4b (nested composite input views: seven examples and most of the
mdtests), the packaged view of input-cursor and the counted population of
bounded-pool (deferred with a refusal), and the three unchanged
expectations.
After 4b (2026-09-13): 8 of 1,512 mdtests and 2 of 27 examples fail. The
remaining items are listed under step 4; three are deliberately unchanged
expectations, two are deferred syntax, and the rest are small mechanisms
outside composite depth.

Reclassify from a fresh run before each step rather than from these counts.

The parked experiment contains these coherent ideas, each of which needs to
be re-derived as a reviewable commit with focused positive and negative
tests rather than restored wholesale:

- A `BorrowedContractInput` loan origin models a top-level `views`
  precondition as authority borrowed from an unknown caller. Its root has no
  close or recovery right, is tied to the exact checked principal resource
  occurrence, supports only reads and nested reborrows, and cannot become
  ownership. It is internal kernel state and adds no syntax. Contract-proof
  entry installs those roots after argument/resource lowering; composite
  input views record a definition-checked one-level child frontier; bindings
  follow exact child occurrences rather than fact equality.
- Direct, named, callback, certification, proof, and loop paths preserve the
  ledger, participant, and occurrence-binding sidecar instead of replacing
  the resource context directly (`with_resource_context` rebases).
- Symbolic borrowed ranges are retained outside the concrete dyadic index and
  checked against current separation assumptions. Bounded local views use
  the existing activation-local bounds rule; exact const/static memory views
  are intrinsic read-only authority.

Two automatic approval reviews are binding constraints:

- A prototype that rooted every view already present in the state was
  rejected: authority may be created only for exact checked contract-input
  occurrences. Principal-occurrence selection is the safe repair; do not
  restore ambient enumeration.
- Admitting nested composite child pieces as ordinary composite backing was
  rejected because the full recursive footprint was not protected. A
  recursive composite view needs a distinct checked representation and an
  enforcing write/lifetime rule, or must stay an explicit refusal. Do not
  flatten a recursive resource or remove the rejection.

The experiment's `LoanLedgerData` gained `unindexed_memory`, an
`indexed_memory` fallback map, and counters so a symbolic write query could
be checked against concrete active roots. That fallback never passed a
focused test or scaling review and its invariant is not stated. Preserve the
fail-closed `active_memory_overlaps`; only the assumption-aware access path
may use a bounded explicit fallback, charged to the explicit symbolic query
or indexed by block, never an ambient whole-ledger scan.

Failure classes from the last candidate corpus run, to be reclassified from
a fresh run rather than trusted:

1. **Returned-view provenance and selected mutable footprints.** Return
   recovery sees two output-view sources: the preserved outer borrowed view
   (handled by a parent-binding lookup) and a view deduplicated against a
   checked returned owner, which still needs an explicit checked provenance
   record. Do not accept a returned view merely because some owner happens
   to satisfy it. Fixtures: `c_step_contract_selected_footprint`,
   `c_named_function_contract_pipeline`,
   `modular_call_requirement_indexes_footprint`, callback footprint cases.
2. **Recursive composite views.** `augment_rotate_callback*` need a view of a
   recursive `shape`; the finite composite loan intentionally refuses nested
   or undecidable frontiers. This is required for the rbtree launch path, so
   an unsupported result does not complete step 4. Design it explicitly and put
   it through adversarial review before implementing.
3. **Composite body facts.** `composite_resource_view_then_mutate`,
   `composite_unfold_many_snapshots`, `frame_many_irrelevant_snapshots`, and
   `opaque_calls_preserve_public_store_fact` hit the deliberate refusal of
   fact-bearing composite backing. Supporting them means recording the exact
   checked facts and the stable dependencies that justify reusing them;
   removing the guard alone is unsound.
4. **Loops and branches.** Loop havoc must use the checked owned entry
   footprint as its validated ranges, and unknown write sets keep failing
   closed; validate a loop's declared ownership before stable-loan havoc so
   the ownership diagnostic is not masked. `proof_branch_pointer_local`
   needs an authority-aware join comparison, with positive same-root and
   negative changed/dropped-root regressions.
5. **Certification.** `struct_conditional_value` passes entry-root selection
   but reports that no checked execution matches its execution mode;
   `pure_click_functions` fails only the stdlib `count` claim. Audit the
   entry-state rebases and the distinction between local aggregate views,
   stdlib lowering, and real external roots.
6. **Expected negative diagnostics.** Several negative fixtures now fail at
   the stable-loan barrier before their historical missing-ownership
   message. Preserve the earlier, more specific validation order where
   possible; change an expected substring only when the new diagnostic names
   the true violated invariant and the positive behavior is already sound.

### 1. Land the borrowed-input root (done 2026-09-13)

Landed as "Install borrowed-input roots for stable contract input views":
`LoanOrigin`, `LoanLedger::borrowed_contract_input`, the per-block symbolic
range map and `permits_memory_access_with_assumptions`,
`c_state_with_borrowed_contract_inputs` installed by the surface proof entry
paths, sidecar-preserving `with_resource_context` rebases on the entry,
certification, and return paths, and the `stable_mode_root_view_*`,
`symbolic_*`, and `borrowed_contract_input_*` regressions. The five
`stable_view_*` fixtures pass under `StableLoans`.

### 2. Land inline helper calls and intrinsic views (done 2026-09-13)

Landed as "Run inline helpers and intrinsic views under stable semantics".
An inline helper body is call-site code: it runs on the caller's resources
and ledger, its stores are checked against the caller's active loans, its
own view clauses lend nothing, and the calls it makes plan from and recover
to the caller's ledger, whose evidence the path keeps. A view of the
activation's own local array, when the caller holds neither an owner nor a
view fact for it, and a view of read-only storage are intrinsic: the call
composes the in-bounds view for the callee without touching the ledger.
Regressions: `candidate_inline_reader_uses_the_callers_checked_resources`,
`candidate_local_array_view_*`, and the `stable_mode_inline_helper_*`
surface tests.

### 3. Fix provenance, loop/branch authority, certification, and diagnostics (done 2026-09-13)

Landed as fourteen commits from four Opus subagents plus one coordinator
fix, integrated together on one gated tip. Candidate corpus after step 3:
23 of 1,509 mdtests and 15 of 26 examples fail, from 45 and 15.

- **Return provenance** ("Give returned stable views a checked projection
  provenance", "Certify a one-call execution theorem from its proof entry
  state"): a view surviving a call boundary must be a checked input child, a
  preserved outer binding, or a live checked projection of a held owned
  occurrence (`ResourceContext::exact_projection_support`); fact equality
  against an ambient owner is still refused. Normalization no longer merges
  a fact whose occurrence carries a loan dependency. One-call execution
  theorems certify from their proof's rooted entry state.
- **Planner partitions** ("Plan symbolic view ranges from their covering
  owner", "Decide symbolic effect separation and open the owners a call
  needs", "Treat an empty composite view as needing no loan backing", "Bind
  every view occurrence the plan composes for the callee"): a symbolic view
  range is backed by the owned occurrence that entails it and the whole
  covering owner is escrowed as one loan (no writable remainder, law 8);
  an unbound view description is neither authority nor a veto when an owner
  covers the requirement; `candidate_memory_ranges_relation` decides
  symbolic separation by the same arithmetic as the overlap oracle; a call
  unfolds exactly the folded owners its own requirements need; every
  composed callee view occurrence carries its binding.
- **Loops, branches, certification** ("Validate loop ownership before the
  stable-loan havoc barrier", "Compare branch-join authority instead of an
  incidental sidecar", "Authorize a pristine return state's empty loan
  population"): declared loop ownership is validated first and loop havoc
  falls back to the checked owned entry footprint, still failing closed when
  an owner cannot be enumerated; a `branch ensuring` successor may carry
  only a loan dependency some arm held; a return state's bindings must be
  authorized by the authority that same state carries.
- **Shared roots** ("Share one borrowed-input root across the proof units
  of a function"): the kernel keeps the installed root per function for the
  verification session, keyed by the exact pre-install entry state, so
  every claim proof, loop proof, and certification of one function shares
  one entry authority.
- **Diagnostics and check order** ("Check owned authority before the
  stable loan barrier", "Give loan refusals the D13 conflict shape",
  "Report a lent local's lifetime end as a loan conflict"): scalar stores,
  free, and realloc run their owned-authority check first, so a write with
  no owner keeps "missing resource fact"; a loan refusal now names the loan,
  its origin, the protected resource, and the attempted range through
  `LoanLedger::memory_access_refusal`; the entry refusal names the `views`
  clause that overlaps the contract's own `owns` clause.

Decided, not changed:

- `global_store_requires_owned_cell` and
  `global_byte_array_rejects_neighbor_ownership` keep failing under
  `StableLoans` with the loan-conflict message. File-scope storage has no
  store-site ownership check (legacy's message comes from a post-execution
  footprint check), and gating the loan check on visible ownership would
  skip it for writes covered only through a folded composite. Their
  expectations become the loan message at step 8.
- `call_havoc_symbolic_write_set` keeps failing at entry: its contract's
  `views p[0..1]` overlaps its own `owns p[0..length]`, which no caller can
  supply. The entry refusal now names both clauses; the expectation flips
  at step 8 because it is also checked under legacy.
- `field_derived_precise_effect_after_metadata_write` is not migrated:
  owning the composite widens the callee's mutable footprint to the whole
  body and breaks the caller's frame under legacy too. It needs a way to
  own a composite while declaring a narrower checked write footprint.

Latent items surfaced, to settle before step 6:

- `compare_loan_dependencies` in `src/kernel/primitives.rs` compares raw
  `ResourceOccurrenceId`s, which are process-local fresh counters, unlike
  `compare_support_graph`, which uses stable entry ordinals. Now that callee
  contexts carry loan dependencies, two structurally identical contexts
  compare unequal; inert under legacy, but a cross-run artifact identity
  will see it.
- `struct_aggregate_helper_view` fails because the planner selects an
  owner at element width 1 while the residual owner is at width 4 over the
  same bytes and `memory_range_covers` refuses any width mismatch; byte-level
  coverage in the shared resource algebra is needed.
- The aggregate-copy path has no store-site owned-authority check, so its
  loan check still precedes any ownership diagnostic; two `String`-typed
  loan refusals (loop havoc in `loops.rs`, branch join in `api.rs`) still
  print the debug form.
- `src/surface/verification.rs` still advises a removed `mutable` clause
  in the outside-the-owned-footprint message.
- Every remaining example failure and the remaining "resource shape is
  outside stable-view support", "composite body facts are unsupported",
  "nested or undecidable composite loan backing", and "cannot package a
  loan-backed viewed body" mdtest failures belong to steps 4 and 5.
  `resource_population_split_body_survives_view` (a population body held
  beside its folded population, refused as a second route to escrowed
  bytes) and `augment_rotate_callback_child_read` (separation only provable
  through a folded recursive owner) also wait there.

### 4. Composite views at any depth (plan, 2026-09-13)

Two adversarial reviews on 2026-09-13 broke two earlier designs for this
step (their findings are in this file's git history at commits "Design
steps 4 and 5" and "Record the second design review"). The plan below is
what survived: the first design's mechanism with its invariant stated
honestly, the reviews folded in as hardening, and no new reasoning about
what a composite contains.

**The invariant.** A valid resource context is a partition: every owned
fact is disjoint from every other fact in it, composites included, at
every depth. That is what the star means, and the kernel maintains it by
construction: unfolding consumes the head, folding consumes the pieces,
calls transfer authority. It is the same invariant step 1 relies on for
memory views. A write needs an owner, and an owner in the same context is
disjoint from every view there, so nothing reasons inside a composite.

**Consequences for composite views, at any depth.**

- A lend escrows the exact head and indexes its direct primitive children,
  as today. Nested composite children become read-only descriptions under
  the same loan with no byte backing; the escrow protects them.
- A contract input view installs the same backing without an escrow; the
  contract's partition is the precondition.
- Reading deeper is projection: `unfold`, `observe`, and `open` of a viewed
  composite issue a `Project` transition (D5) that adds the child
  description to the loan's `permitted` set, with the kernel expansion as
  evidence bound to the ledger predecessor. Read-only, so it needs no
  barrier. Instance children stay refused (D12).
- No new write rule, no separation premises, no footprints.

**Hardening, where the kernel does not yet enforce the invariant.** These
are the reviews' confirmed findings; each is a bug for memory views too.

- Refuse at entry and at call planning a contract whose owned clause
  provably overlaps a viewed composite clause's direct frontier. A deeper
  self-contradiction is unsatisfiable by any valid caller; a proof under it
  is vacuous and harmless.
- Keep refusing a lend of a population whose body is exposed beside its
  head; that is the one kernel mechanism that breaks the partition on
  purpose.
- External contracts stay explicit trust assumptions, as today.
- Route the write paths that bypass the ledger through it: a `free`
  reached through a verified call's allocation delta, call memory havoc,
  loop-exit havoc, and the aggregate copy in call assignment; make the
  loop-head havoc preserve loaned cells instead of erasing them with no
  ledger; count an active loan as active whether or not it has byte
  backing.

**Two cases were first deferred with a clear refusal and are now required
(decided 2026-09-14):** a composite whose body packages a borrowed view and
escapes a call (input-cursor) is step 7; consuming a symbolic quantity of a
body-less token population (bounded-pool) is a planner gap, fixed in 6.2.

**4a landed 2026-09-13** ("Harden the stable-loan barriers and admit body
facts a loan stabilizes", with "Keep a produced composite's body inside
its head" before it). Doing it exposed a legacy soundness bug: the
verified-rule path tracked every non-recursive unconditional composite as
a population and installed a produced composite's body as owned memory in
the caller beside the head, so `make_zero(box); box->value = 5;
read_zero(box)` verified `result == 0` while the program returns 5. The
candidate semantics caught it (the second lend was refused as overlapping
a live footprint). The tracking is off for ordinary composites; every
existing fixture still passes, and
`mdtests/produced_composite_body_stays_inside_its_head.md` pins the store
as a missing-ownership refusal under both semantics. The hardening list
above is done except the two `String`-typed loan refusals that still print
the debug form. Candidate corpus after 4a and 5: 20 of 1,512 mdtests and
9 of 27 examples fail; every remaining example is a nested composite input
view, the packaged view of input-cursor, or the counted population of
bounded-pool.

**4b landed 2026-09-13** ("View composites at any depth through checked
projection"): one checked level at lend and at the root, nested composite
children as permitted descriptions, and projection by the checked `unfold`
and `observe` (`LoanLedger::project`). A projection is derived read-only
authority and keeps the ledger's identity, since loop backedges, branch
joins, and call recovery compare ledgers by identity; the return state of
a body carries the body's ledger so projections authorize its bindings.
Candidate corpus after 4b: 8 of 1,512 mdtests and 2 of 27 examples fail.
The recursive list, tree, and shape fixtures and the seven nested-composite
examples verify. What remains, none of it a composite-depth question:

- `augment_rotate_callback_child_read`: a callee's mutable effect versus a
  lent view from a different caller occurrence; the effect projection
  carries ranges without provenance, so the relation is decided by
  arithmetic and refused as unproved. Needs occurrence provenance on the
  projection, or the partition read at the call.
- `composite_unfold_many_snapshots`, `frame_many_irrelevant_snapshots`: a
  callee views `buffer_storage(owner)` while the caller owns
  `allocated_buffer(owner)`, a different composite whose body covers it.
  Legacy satisfies that by expansion entailment; a loan needs the owner
  unfolded and the viewed composite folded from the pieces, which is the
  V8 owned-interface-to-viewed-implementation adapter for composites.
- `struct_aggregate_helper_view`: the planner selects an owner at element
  width 1 while the residual owner is at width 4 over the same bytes and
  `memory_range_covers` refuses width mismatches (resource algebra).
- `field_derived_precise_effect_after_metadata_write`: needs a way to own a
  composite while declaring a narrower checked write footprint.
- `call_havoc_symbolic_write_set`, `global_store_requires_owned_cell`,
  `global_byte_array_rejects_neighbor_ownership`: expectations deliberately
  unchanged until the step 8 cutover (see step 3).
- bounded-pool: the planner's exclusive reservation demands a direct
  supporting entry for `consumes pool->capacity of pool_slot(pool)` and has
  no "N units of a population whose count is at least N" step; `pool_slot`
  has an empty body, so the ledger is not involved. Fixed in 6.2.
- input-cursor: `input_cursor_init` produces a composite that packages its
  viewed contract input, so the output would outlive the input's loan.
  This is an escaping borrow; step 7.

**Original 4b plan, for reference.** Nested backing in `CompositeLoanBacking` and
`BorrowedContractInputBacking`, the `Project` transition, and the
projection calls in the surface. Regressions for 4b: R14 and R16 with a
two-level list and a recursive shape (read through a child after two
projections; `open` exposes no ownership; recovery restores the head);
negatives: a projection of a child the definition does not contain, a
projection after scope end, one whose evidence names another loan or
predecessor, an instance child, and the entry refusal for an owned clause
inside the viewed frontier.

### 5. Facts in lent bodies (plan, 2026-09-13)

Landed 2026-09-13 with 4a. Recovery restores the exact escrowed head, not
a re-fold, so a fact is re-asserted precisely as folded, and the body is
stable for the whole loan. Refused (`CCompositeResourceDefinition::facts_are_loan_stable`):
a counted population, and a definition whose facts claim liveness of
storage the body does not own; `loadable` over the body's own cells is
stable because a live loan forbids freeing the allocation (D12). On the borrower's side `observe` and `unfold` publish the facts as
observations carrying the loan dependency; a published fact is a
proposition about the snapshot it was read at and is historical after the
loan ends. Regressions: R15 positive (view a fact-bearing composite,
recover, mutate, refold with the fact re-proved), a count fact refused, a
liveness fact refused, and a current-memory reuse after scope end refused.

### 6. Review the complete change adversarially (reviewed 2026-09-13, fixes pending)

**Read:** this entire issue and all implementation handoffs.
**Depends on:** steps 1-5 and a green candidate corpus.

**Boundary:** review and minimal missing regressions/fixes; no new features.
Assign after implementation, preferably to an agent that did not author the
core loan rules. This card does not start such an agent now.

**Work:**

- Check every D2 law against all V0 entry-point consumers. Search for old
  core projection, non-consuming view satisfaction, owner/view absorption,
  return deduplication, local bypass, loop viewed form, and unchecked resource
  rewrite paths. Classify each remaining occurrence explicitly.
- Try to duplicate authority through facts, normalization, substitution,
  branch joins, hidden resource bodies, counted units, and stale snapshots.
  Recheck R01-R32 coverage at its required layer.
- Verify that the full candidate engine has no legacy fallback and that
  extension-model claims match implemented versus model-only operations.
- Review scaling evidence and the planned step 8 removal list. Run the full
  candidate gate on the exact reviewed commit.

**Done when:** all required semantics have an enforcing path and meaningful
regressions, every observed defect is fixed/rechecked, and the coordinator
has an explicit cutover-ready verdict. Unresolved soundness or tooling
concerns block step 8; an optimistic checklist does not replace evidence.

**Review record (2026-09-13, at master d2a80734).** Three independent
read-only reviewers, none of whom authored the loan rules: A attacked the
ledger and authority core, B attacked the call boundary and write paths, C
mapped R01-R32 to their witnesses, ran the candidate corpus, and walked the
step 8 removal list. Corpus at the reviewed commit: 8 of 1,512 mdtests and 2
of 27 examples fail, exactly step 4's list, nothing unexplained. Findings are
numbered F1-F16 and grouped by what they mean for the cutover.

**Verdict: not cutover-ready.** Two confirmed defects (F1, F2), one confirmed
legacy hole that the step 4 plan's premise depends on (F3), and one missing
required regression (R22) block step 8. The rest is hardening, coverage, and
cutover logistics. What held up under direct attack is recorded at the end.

*Confirmed defects.*

- **F1 (B, confirmed, candidate-only regression).** A call whose allocation
  continuity is undecided can retire an allocation whose bytes it lent as a
  view. `apply_verified_heap_allocation_delta` has two retire branches; the
  definite-free branch consults the ledger, the undecided-continuity branch
  scans only `preserved_caller_resources` and skips the ledger barrier. Under
  candidate semantics the owner backing the view has been escrowed out of the
  caller residual, so the scan no longer sees it. Repro: `external_alloc(4)`,
  store 7, call `realloc_like(p, n)` declared `views p[0..4]; consumes
  allocation(p, 4); produces allocation(p, n)`, then read `p[0]`; candidate
  proves `result == 7`, legacy refuses with "resource would remain usable
  after its allocation is freed". Adding the same `memory_access_refusal`
  block before the undecided retire flips the fixture to a loan conflict.
  Closing rule: every path that retires an allocation identity consults the
  ledger that carries this call's own loans; a `preserved` scan is not a
  substitute once lending empties the residual. Same rule for any other site
  still reasoning from `preserved_caller_resources`.
- **F2 (A, confirmed, latent).** `active_memory_loans` is not conserved. The
  `Reborrow` arm increments under `!parent.memory_backing.is_empty()`, the
  `End` arm decrements under `loan_protects_memory(backing, permitted)`,
  which is true for any composite loan. A reborrow of a byte-less composite
  loan (the nested case 4b admits) therefore increments nothing and its end
  decrements the parent's contribution; a unit test (`lend_composite` with a
  token-only frontier, `reborrow`, `transfer`, `end`) fails
  `has_active_memory_loans()` with `invariant_holds()` true throughout. That
  counter is the only barrier such a loan has: with it at zero
  `validate_loop_havoc_stable_loans` accepts an unknown write set and
  `validate_branch_memory_delta_against_loans` returns before reading a cell.
  Not exploitable today only because `recover_stable_views` discards the
  mutated ledger. Closing rule: increment and decrement both use
  `loan_protects_memory`; `invariant_holds` recomputes the counter from the
  live loans.
- **F3 (B, confirmed, both modes).** Composing a produced composite does not
  check its body against facts the destination already holds. `resource
  zz_box3(p) { owns p[0..1]; }`, `extern void repackage(int32* p) { produces
  zz_box3(p); }`, `extern void take_box(int32* p) { consumes zz_box3(p); }`;
  a caller holding `owns p[0..1]` calls both, reads `p[0]`, and still
  discharges its own owner at exit. One owner became two. This is the same
  family as the ordinary-population hole fixed in step 5, and it falsifies
  the step 4 premise that a valid context is a partition maintained by
  construction. Composite views at depth inherit whatever this admits, and a
  cutover makes the premise load-bearing for the whole corpus instead of one
  opt-in mode. Closing rule: composing a produced or ensured composite checks
  its one-level frontier for overlap against the destination's primitive and
  composite facts, as the composite lend already does with
  `remaining.unchecked_with_facts(backing.pieces).validity_error`. Note that
  the lend-side check runs after `owns` requirements leave the residual, so
  it does not see an owned requirement overlapping the lent composite either.

*Kernel shape (plausible, no exploit found).*

- **F4 (A).** `LoanLedger::project` checks that `parent` is a live permitted
  composite and that `child` is a non-instance view, then pushes `child`
  verbatim; containment is delegated to the two surface callers. D2 law 10
  says the kernel checks transition premises itself. Second-order effect:
  `project` keeps the ledger identity, so the branch join, loop backedge,
  `recover_candidate_stable_view_resources`, and `recheck_entry` cannot see a
  projection difference; the join today rejects such arms only because both
  projection sites also add bindings and binding-map identity is compared.
  Closing rule: `project` takes the checked expansion as evidence and
  re-checks containment, and the identity story for read-only extensions is
  stated (either projections change identity and the identity consumers are
  taught to accept the extension, or an explicit projection set is compared).
- **F5 (A).** A reborrow copies the parent loan's whole `permitted` set and
  backing, although one description authorized it; narrowing lives only in
  the planner's `satisfies_fact` checks. Carry the descriptions derived from
  `parent.viewed`.
- **F6 (B).** The call-site mutable-effect check iterates
  `plan.stable_views()` memory ranges, so it cannot see composite views,
  intrinsic views, or empty composite views (filtered out before planning).
  Covered today by two accidents: resource-derived frames derive effects only
  from `owns`, and pre-existing caller loans are checked separately. Compare
  effect ranges against the full checked frontier.
- **F7 (B).** `compare_loan_dependencies` orders `ResourceContext` by
  process-local occurrence and loan identities, unlike
  `compare_support_graph`'s stable ordinals, and it now runs on every
  candidate call. Conservative direction (missed fixpoints and interning,
  not accepted junk) but it must be fixed before artifact identity depends on
  loan dependencies.
- **F8 (B, C).** Returned-input views are removed from the residual one
  occurrence at a time by exact representation, leaving unbound view
  descriptions the planner then special-cases. Separately, the ensured
  return-view deduplication at `functions.rs` ~10711 still runs before the
  provenance routes in both modes; it is defanged, not removed.
- **F9 (A).** Both loan-preserving havocs keep a zero-width cell's value
  without consulting the ledger. Probably unreachable (`CValue::Void` is the
  only zero-width value and nothing stores it into cells); the default should
  still drop the cell.
- **F10 (A, C, scaling).** Per store or free, the symbolic query walks every
  symbolic protected range in the block (bounded, charged). The two
  loan-preserving havocs run that query once per surviving cell: cells x
  symbolic loans x oracle per loop head and branch join. `authorizes_bindings`
  runs bindings x permitted entailments per return path.
  `interface_successor_loans_are_inherited` is a quadratic scan over two
  occurrence-keyed persistent maps, and the binding count grows with proof
  length (one per exposed child per unfold/observe), not with the contract.
  `src/surface/tests/scaling_tests.rs` has no loan curve; the eight four-size
  curves live in `src/kernel/loans.rs`. Add a binding-count curve and a
  cells x loans curve.

*Coverage (C).*

- **F11.** R22 has no test at all (one arm ends a loan, the other keeps it,
  the join must not yield unconditional ownership; D14's worked trace).
  PARTIAL: R01 (no same-value store negative), R03, R04 (no fresh scope
  over the same resource), R07 (no concrete caller with live memory making
  the bad call; the borrow probes are off-gate), R08 (no width-crossing
  overlap), R11 (no retarget after a pointer field write), R12 (no
  certificate-level stale-view negative), R16 (D5's open/close-body
  obligations were folded into read-only projection; the "open obligation
  holding a share" half has no enforcing path), R18 (only two routes pinned),
  R21, R23 (backedge share discard), R26 (tamper side strong, positive side
  unmeasured, see F15), R31 (no `views p[0..0]` regression), R32 (see F10).
- **F12.** `stable_mode_root_view_refuses_an_aggregate_copy_into_it` asserts
  `active loan || missing resource fact`; tighten to the loan conflict.

*Cutover obstacles (C).*

- **F13.** `examples/input-cursor` (composite packaging a borrowed view) and
  `examples/bounded-pool` (counted population with a symbolic quantity) are
  the deferred-syntax cases, and both are documented flagship examples
  (`docs/concepts/larger-examples.md`, `docs/reference/examples.md`,
  `docs/reference/cli/verify.md`, `docs/internals/testing.md`).
  `field_derived_precise_effect_after_metadata_write.md` is a
  `verified-example` in three doc pages. Decided 2026-09-14: neither example
  is quarantined. input-cursor is an escaping borrow and step 7 is required
  before the cutover; bounded-pool is a planner gap fixed in 6.2. The
  `field_derived_precise_effect_after_metadata_write.md` case (own a
  composite, declare a narrower checked write footprint) is still open and
  is decided in 6.3.
- **F14.** Three legacy paths are not behind the mode flag and survive a
  naive cutover: the planner disjunction at `functions.rs` ~10223
  (`candidate && (ledger.is_some() || any view requirement)`, which routes a
  view-free, ledger-free call through legacy planning); `intrinsic_read_views`
  (D10's checked lending from implicit local authority was never implemented,
  a `local:` block prefix plus no caller fact is the whole test, and the R10
  kernel regressions pass only because they install a ledger by hand); and
  the return-view deduplication in F8. Each needs an explicit justification
  as a no-op shortcut or removal.
- **F15.** The CLI registers `CLICK_VIEW_SEMANTICS` but never reads it, so
  `click expand`, `profile`, and `audit` have never run under candidate
  semantics, and `scripts/check.sh` never runs the candidate corpus. The
  acceptance criterion that ordinary verification, expansion, and audit agree
  is unmeasured, and expansion disagreeing with verification is a
  tooling-stability stop condition that is currently unobservable.
- **F16.** Cutover bookkeeping the step 8 card omits: `verify_c0_project_in_mode`
  and the `src/surface.rs` re-exports; `prepare_contract_resources` becomes
  always-true for the two body-execution paths once the `||` disappears
  (audit those callers); `call_havoc_symbolic_write_set.md` must migrate its
  contract (drop `views p[0..1]`, which its own `owns p[0..length]` makes
  unsatisfiable) rather than flip, or the havoc-distinctness property it
  tests is exercised nowhere; the two global-storage negatives flip with
  justification but `global_store_requires_owned_cell.md`'s title and prose
  become false; the body-rerun ratchet baselines in `tests/mdtests.rs` and
  `tests/examples.rs` are skipped under the switch and must be re-pinned;
  the eleven doc locations that state the legacy law (`docs/concepts/
  resources.md`, `spec-state.md`, `docs/reference/language/index.md`,
  `glossary.md`, `docs/internals/separation-logic.md`,
  `design/supporting-more-languages.md`, `view-output-inventory.md`,
  `larger-examples.md`, `docs/reference/examples.md`); the step 3 latent
  items (`verification.rs` ~2547 advising the removed `mutable` clause, two
  debug-form refusals in `api.rs` and `loops.rs`); and the
  `track_ordinary_populations` parameter, which every caller passes as
  `false` and can be deleted in either mode.

*Held under attack.* Recovering a root (origin pinned at issue and apply,
no close right, no escrow); adding two arms' capabilities at a join (ledger,
participant, and binding identities compared first); element-width mismatch
hiding an overlap (both sides byte-normalized before the oracle);
cross-block bucketing (differing blocks are unprovable anyway); symbolic
query beside concrete loans (refused); loan leakage out of a call (exact
parent ledger returned, transitions rechecked from the callee root,
undischarged obligations refuse recovery); reading past the frontier without
a projection; entry-time owner/view overlap; a callee writing what the caller
only views; law 8 with a symbolic owned/viewed pair from one owner; definite
free under a lent view; using duplicated authority inside one call; double
or partial recovery; error and diverging return paths.

**Ordered plan to a cutover-ready verdict.**

- **6.1, mechanical (landed 2026-09-14, "Close the step 6 mechanical
  findings"):** F1 closed by `refuse_retiring_a_lent_allocation`, called on
  both retire paths, with the reviewer's repro pinned as
  `stable_mode_undecided_continuity_retire_refuses_a_lent_allocation`
  (surface, candidate mode, since legacy refuses the same program with a
  different message). F2 closed: the reborrow arm counts with
  `loan_protects_memory`, and `invariant_holds` recomputes
  `active_memory_loans` from the live loans;
  `ending_a_reborrow_of_a_byteless_composite_loan_keeps_the_barrier_armed`.
  F9 closed: both loan-preserving havocs drop a zero-width cell. F12: the
  surface aggregate-copy test was never a ledger witness, because a root
  view has no owner beside it and the write-authority check runs first; it
  now pins `missing resource fact \`owns s[0..1]\`` exactly, and the
  ledger-level aggregate witness is the new kernel test
  `owner_authorized_aggregate_copy_into_a_lent_range_is_refused`. R22:
  `abstract_join_rejects_a_loan_ended_on_only_one_arm` (either arm order
  refused; both arms holding the same recovered ledger join). Candidate
  corpus unchanged at 8 of 1,512 and 2 of 27; gate green.
- **6.2, kernel hardening (landed 2026-09-14, four commits from parallel
  agents, cherry-picked and gated as one tip):**
  - F3 closed ("Check a produced composite's body against what the caller
    holds"): `produced_composite_frontier_conflict` runs in
    `evaluate_contract_return_resources`, the one funnel for the
    verified-rule, refinement-adapter, and direct contract paths. Each
    ensured owned composite is expanded one level and its frontier composed
    into the destination for `validity_error`; the destination is what the
    caller holds across the call, so the plan now records
    `escrowed_owners` and the check unions them in (the reviewer's
    `views p[0..1]` + `produces box(p)` variant slipped past the residual
    alone). Structured refusal
    `CRuntimeError::ProducedCompositeOverlapsHeldResource`. Counted
    populations are exempt because their body is population-wide and is
    checked once where it is installed (`activate_population_body_resources`
    now validates the composition); an ordinary composite with a quantity
    other than a constant one is refused, since every unit would own the
    same range. Regressions:
    `mdtests/produced_composite_body_overlapping_a_held_owner.md` (both
    modes, the F3 repro) and
    `produced_composite_over_a_viewed_owner_is_refused_in_both_modes`;
    positive witness `mdtests/composite_resource_clone_separate_target.md`.
    Known limits, by design: frontier-deep not body-deep; an opaque head
    (no definition, instance schema, matched arm, undecided guard) exposes
    no frontier and composes unchecked as before.
  - F4 and F5 closed ("Check projection containment and narrow a reborrow
    in the kernel"): `project` takes `CompositeProjectionEvidence`, built by
    the kernel from `expand_composite_resource_fact_with_children` over the
    head alone, and refuses a head that is not the permitted parent
    (`InvalidEvidence`) or a child outside the expansion (`MissingBacking`);
    the surface callers build nothing themselves. Identity rule written on
    `project`: a projection is derived read-only authority, mints no share,
    scope, or recovery right, and keeps the ledger identity; identity tracks
    authority-changing transitions only. A reborrow now carries
    `permitted = [parent.viewed]` and only the backing under that
    description (`reborrowed_authority`). Tests:
    `a_projection_mints_no_share_and_keeps_the_ledger_identity`,
    `a_reborrow_narrows_to_the_description_that_authorized_it`,
    `a_reborrow_of_a_memory_view_protects_exactly_the_viewed_bytes`, plus the
    two projection negatives. Open: building the evidence lowers the whole
    environment's definitions per projecting tactic (11 projections across
    the candidate corpus); belongs with F10.
  - F6 and F7 closed ("Close step 6 findings F6 and F7"): the transfer
    records `checked_view_frontier` (composite backing pieces, intrinsic
    read views, empty composite views) and the call-site effect check
    compares every effect range against it with the same two refusals; the
    check no longer requires a plan, since an intrinsic-only call has none.
    `compare_loan_dependencies` and `Hash` for `ResourceContext` key on
    entry ordinals, the viewed fact, and first-appearance positions, never
    arena counters, so identical contexts from different ledgers compare
    equal. Tests: `candidate_rejects_mutable_effect_overlapping_a_composite_view_piece`,
    `candidate_rejects_mutable_effect_overlapping_an_intrinsic_local_view`,
    `candidate_allows_a_mutable_effect_disjoint_from_a_composite_view_piece`,
    `loan_dependencies_from_different_ledgers_compare_equal_and_hash_alike`,
    `loan_dependencies_differing_in_the_viewed_fact_order_deterministically`.
  - bounded-pool closed ("Plan population quantities and check the
    composite lend against reserved owners"): a requirement whose quantity
    is not the unit (`requirement_is_population_quantity`) leaves the stable
    planner's exclusive reservation and takes the counted-population route
    legacy takes, since the caller holds one representative unit while the
    cardinality lives in the tracked population; a memory-bearing population
    body is still checked against the ledger after planning (a barrier with
    no reachable witness yet). The composite lend now composes the reserved
    owned requirements back beside the frontier before `validity_error`, so
    `owns p[0..1]` + `views box(p)` over the same byte is refused as a proven
    overlap. Tests:
    `candidate_symbolic_token_population_consume_plans_beside_a_lent_view`,
    `candidate_token_population_consume_without_a_known_count_is_refused_like_legacy`,
    `composite_planner_rejects_an_owned_requirement_inside_the_viewed_frontier`.
    `examples/bounded-pool` verifies under the candidate semantics with its
    sources and sidecar unchanged.
  - Candidate corpus after 6.2: 8 of 1,514 mdtests (the step 4 list) and
    1 of 27 examples (input-cursor, step 7). Legacy corpus and gate green.
  - After step 7: 9 of 1,516 mdtests (the step 4 list plus the globals
    audit's `rb_augment_callbacks_const_suite.md`) and 0 of 27 examples.
  - After 6.3: 8 of 1,517 mdtests and 0 of 27 examples.
  - After 8a: 2 of 1,517 mdtests (the two global-storage expectation
    flips) and 0 of 27 examples, with the planner running for every call.
- **6.3, decisions (2026-09-14):**
  - **F13, metadata-write fixture: migrated, not quarantined.** The fixture
    was the legacy idiom of an owned piece inside a viewed composite whose
    facts depend on that piece (`len < cap`), which 6.2 refuses as a proven
    overlap and no stable loan could keep. It now owns the composite and
    promises the preserved cell (`ensures owner->data[0] == old(owner->data[0])`);
    the caller frames `data[0]` through that promise rather than through the
    callee's write footprint, and it verifies under both semantics with the
    C unchanged. The two doc pages that cite it (`docs/concepts/aliasing-and-frames.md`,
    `docs/reference/language/index.md`) now say that a narrow write inside a
    composite is ownership of the whole plus an ensures about the untouched
    cells. A checked partial composite borrow (own the head, declare a
    narrower write footprint) is a possible later extension with explicit
    syntax; nothing in the corpus needs it now.
  - **F14(a), planner shortcut: kept through step 8, with its removal cost
    measured.** Removing `candidate && (ledger.is_some() || any view)` and
    running the candidate corpus turned 16 fixtures: 15 negatives whose
    expected `missing resource fact` became the loan-shaped "required loan
    backing or binding is missing", plus two verdict changes. The diagnostic
    half is closed now: a planned owned requirement the caller cannot supply
    reports `CRuntimeError::MissingResource` for that fact (a view the
    planner cannot back stays a loan refusal), which returns 12 of the 15 to
    their expected message under the planner. Three blockers remain for the
    removal and are the step 8 pre-check list: `conditional_resource_branchless_free.md`
    (a conditional composite `owned_item(null)` whose condition is false is
    not discharged by the planner; legacy discharges it definitionally),
    `token_resource_rejects_call_duplicate.md` (a quantity-2 token
    requirement goes through the population route and reports differently),
    and `borrowed_local_view_bounds_rejected.md` (with the planner in charge
    the local view past the block is refused as a read of uninitialized
    storage instead of a missing fact; both refuse, the message changes).
  - **F14(b), `intrinsic_read_views`: classified as a rule, not a hole.** A
    view of caller-local storage the caller holds no resource fact for is
    intrinsic read authority for the call: nothing else can reach that
    storage while the caller is suspended, the callee cannot write through a
    view, and a view returned from the call still has to pass the
    provenance routes. It is neither lent nor recovered because there is no
    owner to escrow. This is D10's "implicit local authority" as an explicit
    rule with no ledger transition; the comment on the selector says so.
  - **F14(c), return-view deduplication: removed at step 8.** Under the
    candidate semantics the dropped views are captured in
    `candidate_output_views` and run the provenance routes, so the filter is
    harmless now; it is on the step 8 removal list already.
  - **F15 closed** ("Make the CLI honor CLICK_VIEW_SEMANTICS"): one parser
    in `src/cli.rs`, installed by the four subcommand entries as the
    process default that `CSourceContext::bundle`/`prepared` and the
    session constructors read (a single static to delete at step 8; an
    unrecognized value is a command error); the two fixture harnesses share
    the parser. Measured agreement pass under `stable-loans`: `verify` of
    all 27 examples exits 0 with proof counts identical to legacy; `audit`
    of input-cursor, bounded-pool, arena, borrowed-slice and the five
    `stable_view_*` fixtures reports no failing site; `profile` runs on all
    of them (arena is certification-bound in both modes); `expand` of one
    claim in each of the four examples and of `stable_view_ordinary_reader`
    yields a rewrite that verifies, profiles, and audits. No disagreement
    between verify, expand, profile, and audit in either mode, so R26's
    positive half is measured. Test
    `verify_honors_the_view_semantics_environment_variable` (the same
    sidecar refused with the footprint message under legacy and the loan
    message under `stable-loans`). Note: `click verify examples/` stops at
    the quarantined `multifile-registry` in both modes; the CLI has no
    quarantine, which predates this work.
  - **F11 partially closed** ("Add fix-views regressions R01, R04, R08,
    R11, R23, and R31"), each confirmed to fail with its guard stubbed:
    `owner_authorized_same_value_store_into_a_lent_range_is_refused` (R01);
    `an_old_descriptor_is_refused_after_a_fresh_scope_over_the_same_resource`
    (R04); `bytewise_overlap_is_decided_across_mismatched_element_widths`
    (R08); `stable_mode_field_derived_view_reads_the_entry_footprint` and
    `stable_mode_field_derived_view_does_not_retarget_after_a_pointer_write`
    (R11); `loop_back_edge_refuses_a_dropped_share_or_a_regenerated_root`
    (R23); `mdtests/empty_view_authorizes_nothing.md` (R31, both modes; the
    nonnull half has nothing to pin, since Click proves `p != 0` from no
    memory clause at all). Still PARTIAL after this: R03, R07 (no concrete
    caller with live memory), R12 (certificate-level stale view), R16 (the
    open-obligation half of D5 was folded into read-only projection), R18
    (route matrix), R21.
  - **F10 closed as far as a local change allows** ("Measure and fix the
    interface-join and havoc loan curves"): `interface_successor_loans_are_inherited`
    was B(B+1)/2 in the binding count (36, 136, 528, 2080 for B = 8..64) and
    is now one membership index over binding values (24, 48, 96, 192),
    pinned by `interface_binding_inheritance_is_near_linear_in_the_binding_count`.
    The loop-head havoc is N^2 + 1 in cells times symbolic loans (65, 257,
    1025, 4097) and no local change fixes it: a symbolic base cannot enter
    the dyadic index, the per-block bucket and empty-bucket early-out
    already exist, and each cell's answer is its own. It is pinned as a
    measurement (`loop_head_havoc_work_over_cells_and_symbolic_loans`, an
    upper bound so a later index change still passes) and recorded in
    `docs/internals/verification-efficiency.md` as a known violation, not
    an exception; the fixed dyadic walk the query paid per cell with an
    empty concrete index is gone. `authorizes_bindings` records no
    deterministic work on its path, so its curve is not landed.
  - Candidate corpus after 6.3: 8 of 1,517 mdtests (the step 4 list minus
    the migrated metadata-write fixture, plus the globals audit's
    `rb_augment_callbacks_const_suite.md`) and 0 of 27 examples. Legacy
    corpus and gate green.
- **Step 7, escaping borrows,** after 6.1 and 6.2 and before the cutover.

### 7. Escaping borrows (required, decided 2026-09-14; landed 2026-09-14)

**Read:** D1, D2, D5, D6, D8, D10, R14-R16, R24, the step 4 plan, and the
step 6 record.
**Depends on:** 6.1 and 6.2.

**Boundary:** kernel loan rules for a composite that packages a view, the
surface elision rule at call boundaries, `examples/input-cursor` verifying
under the candidate semantics unchanged, regressions; no new annotation
syntax beyond the refusal for the ambiguous case.

**Why required.** A composite whose body contains a `views` clause is a
struct that holds a borrow: in Rust terms `struct Cursor<'a> { data: &'a
[i32], pos, len }`. Any C struct with a pointer into memory it does not own
has this shape (iterators, cursors, parsers, string views, slices), and
`examples/input-cursor` is the documented flagship instance. Its constructor
takes `views readable_input(data, length)` and produces
`input_cursor(owner)`; under the loan semantics the input view is a loan
that ends at return, so the produced composite would outlive it and
`fold(input_cursor(owner))` refuses to package a loan-backed viewed body as
an owned composite. Refusing this shape is not an option for a view system
meant for existing C.

**Rules (the mechanism exists; the syntax is mostly elided):**

- A composite whose definition body contains a `views` clause is a
  *borrowing composite*. Folding one makes the folded head a dependency of
  the loan behind each viewed body piece, exactly as a reborrow child is;
  unfolding or consuming it releases the dependency. The ledger already
  refuses ending a loan with a live dependency, so the viewed data's owner
  cannot be recovered while a folded cursor over it is live. No new
  transition kind: the head is a child scope of the backing loan.
- At a call boundary, a produced borrowing composite whose viewed pieces are
  backed by a viewed contract input keeps that input's loan open after
  return, with the produced composite as its dependency. The caller keeps
  the escrow and the close and recovery rights; it recovers its owner only
  once it consumes or unfolds the composite. With exactly one viewed input
  that can back the piece, the binding is unambiguous and nothing is
  written (Rust's lifetime elision). More than one candidate input, or a
  produced borrowing composite that no viewed input backs, is refused with
  a diagnostic naming the composite and the candidate inputs; an explicit
  form can be added later for that case only.
- `views cursor(owner)` on a later function is a reborrow of the composite's
  dependency, one level, as in 4b. `owns cursor(owner)` transfers the struct
  together with its borrow: the callee receives the head as a dependency
  holder, and returning it hands the dependency back. Neither needs syntax.
- A borrowing composite is never an owner of its viewed pieces. Projection
  (4b) of a viewed piece yields a view description; the partition invariant
  is unchanged because the viewed piece is already disjoint from every owner
  by the entry refusal.
- Recovery at return (D8) gains one case: a loan whose only remaining
  dependency is a produced composite is *returned open*, recorded in the
  call plan as an escaping loan, and the caller's ledger carries it. Every
  other outstanding dependency still refuses recovery, as now.

**Regressions:**

- `examples/input-cursor` verifies under `CLICK_VIEW_SEMANTICS=stable-loans`
  with its C and sidecar unchanged.
- Kernel: fold a borrowing composite over a lent range; ending the loan is
  refused with `ActiveDependency` until the head is unfolded or consumed;
  after unfold, recovery succeeds once.
- Kernel: a call that produces a borrowing composite over its viewed input
  returns with that loan open and the composite as its dependency; the
  caller's write into the viewed range is refused while the composite is
  held; consuming the composite, then writing, is accepted.
- Kernel negative: a produced borrowing composite that two viewed inputs
  could back is refused at planning with the ambiguity diagnostic; one that
  no viewed input backs is refused.
- Kernel negative: `owns cursor(owner)` passed to a callee that ends the
  backing loan is refused; the dependency travels with the head.
- mdtests: the cursor constructor, a two-reader over one cursor, and a
  negative where the caller frees the viewed data while a cursor is live.
- Candidate corpus green except the step 6 leftovers still open at the
  time; legacy corpus unchanged.

**Done when:** the rules above have kernel enforcement and regressions,
input-cursor verifies under the candidate semantics, the step 6 reviewers'
attack list (root recovery, join duplication, loan leakage out of a call)
is re-run against the returned-open case, and the record here names the
commit.

**Landed 2026-09-14** ("Land escaping borrows: a folded composite holds
the loan it packages"). What the rules above became in code:

- **Hold.** `LoanHoldId`; `LoanScopeRecord::holds`; `LoanLedger::hold(binding,
  holder)` and `release(hold, holder)`; `End` refuses `ActiveDependency`
  while a scope is held; `invariant_holds` checks the hold index against
  the scopes. A hold keeps the ledger identity, the same rule as `project`:
  it only adds a restriction and mints no share, scope, or recovery right.
  `LoanViewBinding` gained `hold: Option<LoanHoldId>` (also an F7 key), so
  the composite's occurrence carries the hold and every join and recovery
  compares it.
- **Fold and unfold.** `fold` of an owned composite whose body piece is
  bound to a loan places the hold (or reuses the one the piece already
  carries) and binds the head with the piece's description; `unfold` hands
  the binding, hold included, to the restored piece, so a refold places no
  second hold.
- **Call boundary (elision).** `evaluate_contract_return_resources` reports
  the viewed pieces in the one-level frontier of each ensured owned
  composite (`produced_borrowing_pieces`). Recovery backs each piece by
  exactly one loan of the call, matched with `c_resources_directly_match`
  under the certified output facts: a view lent here (the loan is returned
  open; an escrowed owner stays escrowed, a child of the caller's own view
  ends and the parent binding is held), or the hold binding an owned input
  brought in (re-attached to the returned head); none or more than one is
  refused, and a call with no plan at all refuses a produced borrow under
  the candidate semantics. A consumed composite (an owned requirement whose
  occurrence carried a hold and that the callee did not return) releases
  its hold; a root the caller can then close is ended and its owner
  recovered inside the recovery, so the evidence covers it. The evidence
  records the releases and rechecks apply them before the transitions; the
  recovered ledger may now be the rechecked terminal ledger rather than the
  predecessor. Composite lends admit viewed pieces (no byte backing), and an
  escrowed borrowing composite keeps its hold binding across the call.
- **Two incidental fixes.** Recovery composes the recovered escrows into
  the return residual instead of rebuilding the residual fact by fact, so
  the projection support a return publishes survives a later call (the
  pipeline's second call failed provenance without it). The "exclusive
  instance inside a composite view" refusal was also firing on any viewed
  piece; it now fires on instances only.

**Deviations from the card, decided while landing:**

- `input_cursor_take`'s contract is migrated from `views input_cursor(owner);
  owns owner->pos` to `owns input_cursor(owner)`, with an unfold/fold proof.
  The legacy idiom is an owned piece inside a viewed frontier, which 6.2
  refuses as a proven overlap, and the composite's facts (`pos <= len`)
  depend on the piece, so no stable loan could keep them. The C is
  unchanged. The pipeline proof transports `left->len == length` in single
  hops: the transport machinery bridges an origins-unchanged hop or an
  ensures-equality hop, not both in one step (a precision limit, noted for
  6.3, not a step 7 gap).
- **Counted populations are exempt** from the produced-borrow rule, as they
  are from the F3 frontier check: a population unit whose body views an
  object the caller owns and keeps (`mdtests/load_origin_first_seen_per_function.md`)
  is not a struct holding a borrow, and its body enters the caller where
  the population is activated. Population bodies with viewed pieces
  therefore keep the observation reading; a hold for populations is future
  work and is recorded under the step 8 pre-check.
- The ambiguity refusal is implemented but has no surface witness: two
  memory-view inputs can only both back a piece when they are proven equal,
  which the entry partition refuses first. It is exercised by the kernel
  matching only.
- In candidate mode a fold of an owned composite over an *unbound* view
  piece is still admitted (the unbound view can come only from the legacy
  owner-to-view projection, F14, or from unfolding an owned composite whose
  hold lives at a caller); the caller-side rule catches the produced case.

**Regressions:** kernel `a_hold_blocks_ending_the_scope_until_released_and_keeps_identity`,
`a_hold_needs_a_live_binding_and_may_rest_on_a_contract_input_root`,
`escaping_borrow_keeps_the_loan_open_until_the_composite_is_consumed`
(both recovery halves); surface
`stable_mode_escaping_borrow_refuses_a_write_while_the_composite_lives`
(the owner stays escrowed, so the write-authority check refuses first),
`stable_mode_consuming_the_composite_recovers_the_owner`,
`stable_mode_unfold_keeps_the_escaped_borrow_held`,
`stable_mode_produced_borrowing_composite_without_a_backing_input_is_refused`;
mdtest `borrowing_composite_survives_an_owning_call.md` (both modes);
`examples/input-cursor` verifies under the candidate semantics. Candidate
corpus after step 7: 9 of 1,516 mdtests and 0 of 27 examples: the step 4
list plus `rb_augment_callbacks_const_suite.md`, which arrived with the
globals audit while step 7 was gating and fails under the candidate
semantics at that base as well (a call returns a view of file-static
storage that no provenance route accepts; tracked with
`issues/global-variables.md` and the 6.3 coverage items, not a step 7
regression). Legacy corpus and gate green. The step 6 attack list against the
returned-open case (root recovery, join duplication, loan leakage out of a
call) is a review item for the step 8 pre-check rather than something this
landing re-ran.

### 8. Cut over, document, and close (in progress: 8a landed 2026-09-14)

**Read:** the step 6 verdict/removal list and final acceptance below.
**Depends on:** step 6.

**Boundary:** default entry interpretation, removal of temporary rollout
scaffolding, public docs and affected expectations; no new semantic design.

**Work:**

- Make stable views the sole ordinary-memory interpretation. Remove
  legacy independent view creation/fallbacks and temporary mode selectors:
  the `Legacy` variant of `ViewSemanticsMode`, `verify_c0_sources_in_mode`,
  the `CLICK_VIEW_SEMANTICS` variable in `tests/mdtests.rs` and
  `tests/examples.rs`, and its entries in `src/cli.rs`,
  `docs/reference/cli/environment.md`, `docs/reference/inventory.toml`, and
  `docs/internals/testing.md`. Retain only justified owner observations,
  scoped views, and explicit family-specific persistent facts.
- Update `docs/concepts/resources.md`, affected examples, proof/tool docs,
  and the stable-versus-historical descriptions in the shared language
  design. Explain temporary stability, owner reads, partial borrowing,
  scoped recovery, and supported escaping-output limits.
- Preserve the final rules, representation rationale, model assumptions,
  and test map in durable resource/internal documentation before deleting
  this issue. Future agents must not lose the design when the issue closes.
- Run focused changed tests and the unfiltered `scripts/check.sh` on the
  final default configuration. Check the clean primary base and integrate
  only the tested coherent commit.
- Delete this issue and its README entry only when all final acceptance
  criteria hold. Update links that pointed to it.

**Done when:** stable memory views are actually enforced everywhere in the
supported C verifier, the rollout path is gone, the docs describe shipped
behavior, the full gate passes, and the rbtree launch remains the roadmap.
If this step requires a new semantic fix, return it to the relevant step and rerun
the affected review; do not improvise it inside the final documentation step.

**8a landed 2026-09-14: the candidate corpus is green except the two
expectation flips, with the planner running for every call.** Six commits,
five from parallel agents and one contract migration, cherry-picked and
gated as one tip:

- **Composite view backed by the caller's own authority** ("Back a viewed
  composite by an owned description of the same authority"). A viewed
  composite `C` the caller does not own is backed when `C`'s kernel
  one-level expansion is covered piecewise by owned authority the caller
  holds and `C`'s definition facts already hold at the call (lowered at a
  state binding the definition's parameters and discharged by the exact
  routes, never assumed). Two forms: an owned composite `D` whose frontier
  covers `C`'s (D's head is escrowed and `views C` joins the loan's
  permitted descriptions, `CompositeLoanBacking::adapted`), and the
  caller's owned frontier itself (`owns C` is materialized from exactly
  those facts, escrowed, and recovery restores exactly them,
  `CompositeLoanBacking::restored` / `adapter_restorations`). The two
  snapshot fixtures needed the second form: their twelfth call happens
  after `unfold(buffer_storage(owner))`, so the caller holds the frontier as
  primitives. Refused: uncovered frontier, unestablished fact, counted
  population, recursive definition, loan-unstable facts, a borrowing
  composite (its fold needs a hold), and a view the caller already holds.
  A same-composite owner is always preferred. Four `candidate_composite_view_*`
  tests.
- **Bytewise memory coverage** ("Decide memory coverage and subtraction
  bytewise"). `memory_range_covers`, `split_memory_range`,
  `merge_memory_ranges`, and the normalization index re-spell a pair into
  one element width (or compare byte footprints when the bounds do not
  divide); `memory_range_covers_for_read` is gone. Typed loads and stores
  are untouched. `struct_aggregate_helper_view.md` passes under both modes;
  the one pre-existing test that asserted the old width refusal is
  rewritten. **Found, not closed:** `memory_ranges_proven_overlapping`
  still refuses on a width mismatch, so the memory family's
  `pair_validity_error` admits two owners over overlapping bytes at
  different widths; byte-normalizing it makes
  `mdtests/resource_witness_fold_infers_origin.md` fail under legacy,
  because that contract holds `consumes object(node)` beside
  `owns node->word` over the same bytes. That is a partition violation the
  corpus relies on and is fixed in 8b (oracle normalized, fixture contract
  migrated).
- **Effect versus view by provenance** ("Decide a call's effect/view
  separation by occurrence provenance"). The plan records the caller
  occurrence each reserved owned requirement came from, the projection
  records which requirement produced each effect range, planned and
  frontier views carry their support, and an effect and a view from
  distinct occurrences are disjoint by the partition invariant without the
  arithmetic oracle; equal supports, missing provenance, or an ambiguous key
  fall through to the arithmetic check and its two refusals unchanged.
  `augment_rotate_callback_child_read.md` verifies (faster than legacy).
  Tests `candidate_allows_a_mutable_effect_reserved_from_another_owned_occurrence`,
  `candidate_rejects_a_mutable_effect_overlapping_a_view_from_its_own_occurrence`.
- **Returned view of read-only storage** ("Accept a carried view of
  read-only storage at a stable-view return"). The refused view was the
  caller's own three contract-input views of a `static const` table merged
  into one fact; entry treats a read-only block as intrinsic read authority
  with no ledger root, and the return provenance had no matching route. It
  now accepts a carried view whose block is read-only, the same block test
  as both entry sites; a returned view of mutable storage the caller did
  not lend is still refused. Tests `candidate_accepts_a_carried_view_of_read_only_storage`,
  `candidate_rejects_a_carried_view_of_mutable_storage`,
  `stable_mode_carries_a_file_static_const_view_across_a_call`. Noted: the
  return site asks the caller's memory and the entry site the callee's for
  the same block property; no reachable block differs today.
- **Planner shortcut removed** ("Run the candidate call planner for every
  call"). The three blockers closed: an owned composite requirement whose
  expansion is empty (a false guard) is consumed definitionally, as
  `empty_composite_views` already are (an undecided guard keeps its entry);
  the reservation reports the whole constant demand of a repeated token
  (`owns can_complete(cb) (quantity 2)`); the activation-local bounds rule
  refuses an out-of-bounds intrinsic view as a missing resource before any
  read. The twelve negatives 6.3 measured keep their messages. Tests
  `candidate_conditional_composite_with_a_false_guard_needs_no_owned_entry`,
  `candidate_conditional_composite_with_an_undecided_guard_still_needs_its_entry`,
  `candidate_repeated_token_requirement_reports_the_demanded_quantity`,
  `candidate_local_array_view_out_of_bounds_is_refused` (tightened).
- **`call_havoc_symbolic_write_set.md` migrated.** The positive caller owns
  the loaded cell outright and still cannot keep `old(p[0])` across the
  call; a view cannot overlap an owner, so the two callers no longer share
  a contract shape, and the fixture's prose says it no longer pins the
  identical-shape case.

Candidate corpus after 8a: 2 of 1,517 mdtests (`global_store_requires_owned_cell`,
`global_byte_array_rejects_neighbor_ownership`, the two flips) and 0 of 27
examples. Legacy corpus and gate green.


## Decision and violated invariant

Requested on 2026-09-11. Investigation base:
`79411f40e838c61af87a4424a0d483044a30cf67`.

**Change ordinary memory `views` to mean a shared borrow whose covered memory
remains unchanged and allocated while the borrow is active.** Keep `owns` and
`views` as the main surface distinction. Introduce checked lending and recovery
of authority instead of deriving an independently usable view while retaining
a usable writer. A view is temporary stability, not permanent immutability.

The required invariant is: an active shared borrow of ordinary memory cannot
coexist with authority that another proof component can exercise to write,
free, or end the lifetime of that memory. Copying a view description must not
let its holder access memory after the borrow ends. This must hold across
calls, callbacks, resource abstraction, and eventually thread boundaries.

Current Click does not enforce that invariant. This is a design gap for shared
borrowing and concurrency, not evidence that today's sequential verifier
accepts false postconditions: its memory snapshots and checked effects track
intervening writes. C0 currently has no concurrency model. Do not claim that
changing views alone adds concurrent C or Rust support.

The recommendation supersedes the earlier investigation's advice to preserve
weak C views because valid C permits aliasing. The same C can be proved with
different contracts; the probes below demonstrate two such migrations.

This is P1 by explicit user direction: fix the core view semantics before
launch, using the small concurrency and borrowing checks below to assess the
design. The launch remains P1 -> minimum viable rbtree -> public launch.
Production concurrent C and Rust frontends remain later work. The separate
P1 [basic C++ issue](basic-cpp-support.md) exercises these resource rules in a
small additional-language frontend; the broader design lives in
[Supporting more languages](../design/supporting-more-languages.md).

## Evidence from the current implementation

Follow symbols rather than relying on line numbers:

- `src/kernel/primitives/resource_algebra.rs`: `access_mode_core` projects
  an owner to a view; `consume_memory_resource_fact` returns `Preserve` for
  a view requirement. `MemoryResourceAlgebra::pair_validity_error` rejects
  overlapping owners, but not owner/view overlap. `memory_write_range` and
  `memory_resource_fact_permits_write` look for owned range authority.
- The same file's `combine_memory_resource_facts` and
  `combine_exact_resource_facts` can absorb a view into its owner. A real
  outstanding loan must never disappear through this normalization.
- `src/kernel/functions.rs`: `prepare_contract_resource_transfer` and
  `evaluate_contract_return_resources` borrow through entailment, deduplicate
  returned views, and publish supported core projections. These paths need a
  checked loan transition, not an extra check only at direct stores.
- `src/kernel/primitives.rs`: `ResourceContextStorage::supported_by` and its
  reverse index track projections supported by an owned resource. These are
  useful implementation groundwork, but are not transferable shared loans.
- `src/kernel/proof/execution.rs` and `src/surface/proof/resources.rs`:
  observation and scoped opening project views from resource bodies. Freezing
  all such derived entries would inadvertently freeze ordinary owners.
- `src/kernel/eval/statements.rs` checks resource write authority for external
  memory. `prepare_contract_resource_transfer` also special-cases in-bounds
  views of caller-local storage. A future loan check must cover stack storage
  too; allocation or a `local:` block name must not bypass a live borrow.
- `docs/concepts/resources.md` explicitly says views do not prevent owner
  mutation and cannot alone support a folded fact about mutable memory.

Two positive migration probes ran through ordinary bounded `click verify`,
with exit status 0, using the existing verifier source at this base:

1. [alias-owned.click](../design/borrow-probes/alias-owned.click) verifies the
   unchanged [alias.c](../design/borrow-probes/alias.c), retaining `owns p[0..1]`
   and `requires p == q` but removing `views q[0..1]`. Ownership of the location
   authorizes both the store through `p` and the read through `q`.
2. [field-split.click](../design/borrow-probes/field-split.click) changes a
   setter's `views cell(n); owns n->value;` to
   `views n->next; owns n->value;`. Its C is copied unchanged from
   `mdtests/composite_piece_caller_frames_viewed_field.md`. The caller still
   owns the folded cell and proves `n->next == old(n->next)` after the call.

Reproduce from the repository root:

```sh
cargo run --bin click -- verify design/borrow-probes/alias-owned.click
cargo run --bin click -- verify design/borrow-probes/field-split.click
```

These establish that the demonstrated contract migrations work today. They
do not check the proposed loan rules or establish the cost of migrating the
whole corpus. The earlier weak-view alias probe remains historical evidence.

## What stability means

| Resource or operation | Required interpretation |
| --- | --- |
| `owns memory(R)` | Exclusive usable authority over the selected range; direct reads need no separate view. |
| `views memory(R)` | Shared, read-only authority for a borrow scope; covered contents and allocation lifetime stay stable. |
| Two views of overlapping memory | Allowed; readers need not prove disjointness. |
| Usable ownership plus an active independent view of overlapping memory | Incompatible. The lender may retain a recovery entitlement, not usable write authority. |
| Ownership and view of disjoint fields/ranges | Allowed; writes to the owned part preserve the viewed part. |
| An observation supported by ownership | Internal access to that ownership, with snapshot/support checks; not a separately transferable stable view. |
| View of a structural resource | Preserves its selected structure, memory dependencies, and advertised facts for the borrow scope. |
| Shared handle to a mutex or another mutable protocol | Preserves the protocol, not each payload value; accessing payload requires that protocol's checked authority. |

For ordinary memory even a same-value store conflicts with a view: stability
must exclude conflicting access, not just prove equality before and after.
Initialization writes, bytewise stores, deallocation, object-lifetime changes,
and opaque call effects must obey the same authority rules. Snapshots remain
necessary; after a borrow ends, its old observations do not automatically
become facts about later mutable memory.

A view freezes the range selected at borrow entry. It cannot silently retarget
itself when a pointer-valued field changes. Structural resource dependencies
must be covered by the borrow, and a view of a pointer cell does not by itself
freeze the pointee. Preserve existing bounds, initialization, and allocation
checks alongside authority.

## Recommended mechanism: scoped loans with checked access tokens

Use a lifetime-indexed shared loan. The following is design notation, not
Click syntax or an implemented kernel API:

```text
begin scope k                         -> Live(k, 1) + Close(k)
lend Own(R) into k                    -> View(k, R) + Recover(k, R)
split Live(k, q)                      -> Live(k, q1) + Live(k, q2)
                                        where q1 > 0, q2 > 0, q1 + q2 = q
read with View(k, R) and Live(k, q)    -> read covered memory; retain both
end with Live(k, 1) and Close(k)      -> Dead(k)
recover with Dead(k) + Recover(k, R)  -> Own(R), consuming Recover(k, R)
```

Lending requires evidence that `k` is active and moves the owned resource into
checked loan storage. `View` is a copyable description; `Live` is conserved,
splittable authority. All live shares for a scope total at most one. Ending
requires the close entitlement, full share, and all outstanding access/opening
obligations to be closed. If an access temporarily exposes underlying
resources, it holds its live share until those resources are returned.
Recovery happens exactly once
per lent resource. Scope identities are fresh; an old description cannot
become usable again when a later borrow starts.

This gives a concrete fork/join account: each reader gets a view description
and part of the live token. The lender cannot end the scope while a reader
retains its share. Joining and collecting the shares allows ending and
recovery. Merely deleting a view from one local proof context proves nothing
about descriptions or access authority held elsewhere.

The initial surface can leave `k` and token splitting implicit for ordinary
function/loop borrows. Use exact kernel-checked split/join certificates;
fractions are not runtime reference counts and need not appear in routine C
contracts. Keep permission shares separate from today's resource population
counts. D4 chooses a binary split/join tree for the initial representation;
the fractions here are explanatory notation. D5 specifies the remaining
registration, opening, and closure side conditions. Do not implement an
unbounded scan of pointers or view copies.

This protocol is informed by existing lifetime logics: RustBelt separates
type ownership and sharing, and ties access to live lifetime tokens;
VeriFast gives concrete begin/end, borrow, and fractured-borrow operations.
They demonstrate why copyable shared-reference descriptions can coexist with
controlled recovery. They are precedents, not a proof of Click's proposed
implementation. [RustBelt, sections 4-5](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf),
[VeriFast lifetime logic](https://verifast.github.io/verifast/rust-reference/lifetime-logic.html)

### Alternatives considered

- **Keep weak views and prohibit sending them to threads.** Potentially sound
  with an additional sharing mechanism, but it leaves ordinary views without
  the desired stability guarantee and makes Rust references use another
  concept. Prefer one stable surface meaning.
- **Require full fractional permission to write and any positive fraction to
  read.** A suitable substrate for ordinary shared memory. Fractions split and
  rejoin rather than duplicate freely. Alone this changes the current view
  choreography and does not express lifetime-indexed, copyable Rust reference
  descriptions; combine it with scoped loans where useful.
  [Permission accounting in separation logic](https://www.cs.cmu.edu/afs/cs.cmu.edu/project/fox-19/member/jcr/www15818As2011/permacct.pdf)
- **Keep the core law and reject writes when a local view is found.** Insufficient:
  projections already accompany owners, normalization can erase views, and
  copies may reside in another thread or abstraction. The borrowing transition
  must remove usable write authority and conserve recovery authority.
- **Make every view permanent.** Stable but prevents later mutation or
  deallocation; inappropriate as the default for temporary readers.

## Detailed kernel and surface design

### D1. Public meaning and the P1 boundary

The supported C surface keeps ordinary `owns` and `views` clauses. An input
view lasts from the checked call-entry transition through the checked
call-return transition. It is not shortened to the last syntactic load.
Ownership authorizes reads directly; a read through a second equal C pointer
does not require creating a second view.

P1 must implement stable shared loans, scoped recovery, nested read calls,
partial-range lending, ordinary resource abstraction, local/heap/global
protection, and the corresponding proof/call/loop rules. It must also permit
stable memory facts in a resource whose support consists of active views.
Ordinary sequential C remains the implementation target.

The checked design model must additionally cover context splitting for
threads, exclusive child reborrows, returned field loans, and abstract
mutable protocols. These extensions need not acquire Surface Click syntax
or production C/Rust execution in this issue. Keep their operations separate
from supported operations and identify which model transitions have actual
kernel counterparts. Passing their model tests does not mean Rust references,
concurrent C, mutex implementations, or a C memory model are verified.

Do not add explicit lifetime parameters to every ordinary C contract. Do not
add an alternate user-visible weak-view mode. Escaping resource loans (an
output composite that packages a viewed input) are supported by the elision
rule in step 7, with explicit syntax only for the ambiguous case; returning a
C pointer value remains supported where its ordinary C lifetime and the
caller's permissions permit it. Returning a pointer by itself does not return
a loan or extend the allocation's lifetime.

### D2. Non-negotiable laws

The later chunks implement these laws together. A local test of a `frozen`
flag is insufficient.

1. **Authority conservation.** A byte range's write authority is usable in
   one component, suspended in a loan, or transferred to another component.
   Suspending it never leaves another usable copy in a folded owner,
   implicit stack capability, callback frame, or remembered composition.
2. **Reader stability.** While a view has valid access authority, every
   compatible component is unable to write or invalidate its covered bytes.
   This includes equal-value stores, initialization, free/realloc, and
   lifetime end. It is an access restriction, not an equality check afterward.
3. **No view-to-owner entailment.** Recovering ownership is a state transition
   requiring closure evidence and the unique recovery entitlement. Neither
   entailment, normalization, folding, nor a pure theorem can perform it.
4. **Descriptor/authority separation.** Copying, dropping, or deduplicating a
   description changes no live access share and no recovery entitlement.
   Descriptions may survive a scope; their authority does not.
5. **Exact identity.** Scope, loan, allocation lifetime, resource occurrence,
   and support generation are semantic identities. Equal pointer spellings,
   equal resource terms, equal byte values, and reused local names do not
   identify them.
6. **Supported facts retain support.** An owner-supported observation is
   usable only through its current support. A loan-supported observation
   additionally needs the correct active loan access. A fact about an old
   snapshot remains a historical fact, never implicit authority over memory.
7. **Locality.** A valid update remains valid when an unrelated compatible
   frame is present. Rule checking touches the named authority and affected
   dependencies, with indexed access, rather than scanning the whole frame.
8. **No authority from unknown aliasing.** A consuming/lending partition must
   have checked separation or shared backing. Failure to prove overlap is
   not proof of disjointness. Two read requirements may alias.
9. **Branch conservation.** Alternative program paths may each reason from
   the entry resources. A join cannot add their capabilities together.
   Concurrent contexts require an actual disjoint capability partition.
10. **Checked orchestration.** Surface tactics, contract lowering, and smart
    search propose transitions. The kernel checks them independently against
    the actual predecessor state and its evidence.

For each operation below, document an inductive argument that it preserves
these laws, including its behavior with a compatible external frame.
Bounded enumeration is a regression technique, not an unbounded soundness
proof. The frame-preservation requirement follows the separation-logic
approach discussed in the [Iris notes](https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf);
the concrete representation here is a Click design proposal.

### D3. State representation and ownership boundaries

Use persistent, indexed state alongside the existing resource context. The
names below describe responsibilities, not mandatory Rust type spellings.
Do not put live capabilities in `PureFactContext`, ordinary duplicable
propositions, or surface-only metadata. They must participate in checked
resource-state transitions and proof-state identity.

| Component | Required information and owner |
| --- | --- |
| Scope record | Fresh semantic ID, active/ended state, root access-share identity, unique close entitlement, and directly registered loan/opening dependencies. |
| Loan record | Fresh ID, scope, selected family/resource, entry-selected footprint, backing authority identity/generation, and restoration destination. |
| Escrow | The actual suspended owned pieces, including the selected quantity of non-memory resources and any restoration recipe for their packaging. Not searchable as usable ownership. |
| View description | Loan ID and permitted projection/range; no independent read or write capability. Immutable descriptions may be shared. |
| Access share | A conserved capability for an active scope. It may authorize several descriptions in that scope, but cannot be duplicated across concurrent holders. |
| Recovery entitlement | A unique claim to recover a particular escrow after its closure conditions hold. It confers no access while suspended. |
| Supported observation | Exact owner occurrence or loan ID, support generation, memory snapshot/epoch dependencies, and any required access-share/opening evidence. |
| Opening obligation | The selected resource body/protocol opening, held access share, required closing resources/facts, and parent dependency. |
| Transition evidence | Rule, predecessor identity, consumed capabilities, created capabilities, range/guard proofs, support changes, and successor identity. |

Keep `CResourceSpec`'s validated term/access/quantity/role/snapshot envelope.
It describes a contract requirement; it does not itself carry a runtime loan
capability. Instantiate hidden scope bindings at a checked boundary.
`CResourceQuantity::Count` is a resource population quantity, not a lifetime
fraction. Do not overload it or make existing counted resources arbitrarily
divisible.

The existing resource store has occurrence IDs and persistent indexes.
Use occurrence/generation identity for authority that can be consumed and
recreated. An equal `CResourceFact` is not sufficient evidence that it is the
same authority. Counted normalized entries need explicit quantity residuals
or selected-unit provenance rather than pretending the whole population was
lent. Support maps keyed only by a fact must be audited at this boundary.

Store the loan ledger in the checked state root, or in an equivalent resource
carrier included in that root. It must be shared by ordinary evaluation,
modular calls, proof execution, and certification. An execution path cannot
update memory while a second, disconnected ledger says its ownership is
suspended. A future concurrent composition combines compatible capability
fragments against the same authority interpretation, not independent mutable
copies of an authoritative ledger.

The API should have this division of responsibilities. This sketch is
proposed internal pseudocode, not code to paste into the crate:

    propose_call_transfer(interface, entry, support_evidence)
        -> TransferPlan + UndischargedObligations
    check_loan_step(current_proof_state, proposed_step, evidence)
        -> CheckedLoanStep | LoanRefusal
    apply_checked_step(proof_object, checked_step)
        -> successor_proof_object
    authorize_read(current_state, pointer, byte_width, authority_witness)
        -> CheckedReadAuthority | AccessRefusal
    authorize_write(current_state, pointer, byte_width, authority_witness)
        -> CheckedWriteAuthority | AccessRefusal
    project_supported_observation(current_state, support, projection_evidence)
        -> SupportedObservation | ProjectionRefusal

Proposed steps cover Begin, Lend, ReborrowShared, Split, Join, Project, Open,
CloseBody, End, and Recover. Only the kernel creates checked results.
A checked result is bound to one predecessor state/transition identity;
reusing it against a different successor does not create another spend.
A cached result may
re-prove the same judgment but cannot duplicate the underlying resource in
one composition.

For ordinary direct reads an ownership witness is sufficient. For a borrowed
read the witness selects a descriptor and active access capability. Write
witnesses select usable ownership, never a recovery entitlement. Implicit
local authority must produce equivalent checked evidence. The lookup layer
may find candidate witnesses by index, but a boolean from surface lowering
cannot be accepted as the witness.

The transfer plan should record, by contract clause: the evaluated term and
entry snapshot, selected owner/loan occurrence, any range split/coverage
evidence, caller residual, callee authority, scope binding, returned-access
obligation, and packaging restoration evidence. Common call/return code
consumes this record. Do not independently recompute a second mutable
footprint or independently rediscover which loans to recover on return.

Use structured internal refusals for unavailable authority, stale scope,
wrong share, unresolved/proven overlap, active opening/child, missing return,
invalid restoration, and unsupported escape. Existing public runtime/proof
errors can wrap these categories. Keep the checked result and refusal types
opaque outside their validating module.

### D4. Access shares: a concrete first representation

Use a checked binary split/join tree for live access shares in the first
implementation. The fraction notation above explains the semantics; arbitrary
rational arithmetic is not required. A root token represents the full share.
Splitting consumes one leaf capability and creates two fresh sibling
capabilities. Joining consumes those exact two siblings and recreates their
parent capability. Only the reconstructed root can close its scope.

Each tree node has an interned ID and constant-size parent/child links.
Splitting an already split or unavailable leaf fails. Joining repeated leaves,
non-siblings, leaves from another scope, or an ancestor with its descendant
fails. The active capabilities form a disjoint frontier of that tree.
A read checks the active leaf and scope by indexed identity; it does not
walk to the root. Repeated halving must not store increasingly long bitstrings
or denominators in every token.

This deliberately gives a simple sufficient sharing discipline. Arbitrary
real/rational fractions, reassociation of unrelated roots, and a symbolic
fraction solver are unnecessary for P1. A caller can split and return a
leaf for each nested reader. Collecting a split subtree costs the explicit
join operations in its certificate. General fraction syntax, if later
needed, must preserve these conservation and complexity properties.

Add a unique close entitlement separate from the root access token. Holding
all access shares allows reading; closing also requires ownership of that
entitlement and satisfaction of the scope's obligations. This keeps authority
to use a scope separate from authority to retire it. The initial caller
retains close/recovery entitlements while lending access to a callee.

Capabilities are conserved even if the implementation's persistent data
structures are clonable. Cloning a proof state creates alternative proof
paths, not two resources that may later be composed. If a share is discarded,
the program may lose the ability to recover; the checker must not reconstruct
the missing share from a reader count reaching zero. Do not make recovery
depend on Rust host-language destructors or garbage collection.

### D5. Transition rules and side conditions

The operation table is the contract for the kernel implementation. Every
refusal leaves the predecessor state unchanged; failed candidate search must
not partially consume authority or advance the published scope state.

| Operation | Required evidence | Result |
| --- | --- | --- |
| Begin | Fresh scope identity rooted in this checked execution | Active scope, full access token, unique close entitlement |
| Lend owned piece | Active scope, capability authorizing registration, usable ownership, checked range/quantity selection | Selected ownership in escrow, recovery entitlement, scoped description; untouched residual stays usable |
| Reborrow shared piece | Fresh child scope, active parent description/access, checked coverage | Child description and a dependency holding parent access until child closure; no duplicated escrow ownership |
| Split access | Available leaf for an active scope | Consume leaf, produce two fresh siblings |
| Join access | Both available siblings from the same split | Consume siblings, restore parent |
| Project description | Checked subrange/body projection from an existing description | New description with the same loan and required dependencies; no new share |
| Read through view | Active matching scope, available share, valid description/backing, range coverage and normal memory checks | Loaded value and snapshot evidence; same authority afterward |
| Open borrowed body | Available matching share and checked family sharing rule | Scoped body access and a pending close obligation holding that share |
| Close borrowed body | Required body resources/facts restored with unchanged protected support | Discharge opening, return held share |
| End scope | Close entitlement, full root share, no open accesses or dependent child scopes | Consume close/access authority; mark scope ended; release any access pinned from parents |
| Recover | Ended matching scope, unique recovery entitlement, intact escrow/restoration obligations | Consume entitlement/escrow; restore owned resource exactly once |

Registering a loan requires actual usable authority; an active-scope marker
alone is not authority to lend. For P1 a boundary creates its fresh loans
before dispatching their access. If a nested call needs another independent
owner, open another scope for it. Do not extend an already distributed scope
through an unchecked side channel. The model may later generalize registration
with an explicit extension rule.

The scope can own several disjoint escrow pieces. Ending it is not recovering
each one; recovery is separately checked per entitlement. Index its direct
obligations and escrows so the end transition does not scan every past
descriptor. Closing work may be proportional to the explicit objects being
closed, and recovery to the explicit pieces being restored.

Scope IDs must never be reused within a proof identity domain. Use fresh IDs
with provenance from the checked execution/fork; two branches that choose
the same numeric local counter must not accidentally name the same loan.
After closure, historical descriptions can be retained without retaining a
live capability. Retire unreachable bookkeeping when possible; preserve the
certificate identity needed to reject stale evidence. Do not keep all dead
descriptions in the hot lookup set forever.

### D6. Footprints, aliasing, and recovery of packaging

Select memory at entry as allocation-lifetime identity plus a checked byte
range and its source-level view. Preserve element width and existing
overflow/bounds rules when translating field or typed-array ranges. Overlap
must be checked in bytes: an int-sized owner and a byte view can conflict.
Store evaluated pointer identities; do not recompute the footprint from a
mutable pointer field when the call returns.

An empty range grants no dereference and protects no bytes. Preserve the
existing language rules for forming the range; do not infer nonnullness or
a live allocation from an empty permission. A nonempty subrange loan prevents
freeing or reallocating its entire containing allocation, even if unrelated
bytes remain owned. A loan's protection of allocation lifetime is not an
allocation/deallocation capability.

Partition an owned range when lending only part. For example, lending
`a[2..4]` from `owns a[0..8]` leaves `a[0..2]` and `a[4..8]` writable.
Recover only `a[2..4]` and normalize compatible owned residuals afterward.
Sibling fields that occupy distinct bytes remain independently writable.
A view of a pointer cell protects that cell; it does not recursively protect
the pointee unless the resource body explicitly includes it.

Two overlapping read requirements should use shared backing, not attempt
to escrow the overlap twice. For identical requirements, create one loan
and two descriptions. For partial overlaps, use a checked union/partition
of the required ranges or a covering existing owned range whose lending
does not suspend other authority promised by the same contract. Retaining
the unrequested owned remainder is the preferred behavior.

Do not require the caller to decide whether two read-only symbolic
parameters are equal just to pass both. It is sufficient to establish that
both descriptions are covered by the selected loan backing, allowing
overlap. When independent owned sources supply them, their composition
already supplies separation evidence. A general symbolic union requiring
case analysis may use explicit checked cases; silently assuming separation
or lending twice is forbidden.

Loan backing and resource packaging are separate. Lending from a folded
owner may expose only the selected body frontier and suspend the parent
head's independent usability. Keep a restoration recipe for the remaining
pieces and their facts. A parent cannot stay usable as a second route to the
escrowed bytes. Reassembly after return must check the body's advertised
facts in the resulting state; a disjoint permitted write may require
updated model arguments or a new fold proof. Do not restore a pre-call
composite fact just because its memory permissions were returned.

### D7. Read authority versus observations and pure facts

An owner may read directly and inspect its composite without issuing a
stable loan to itself. Replace the ambiguous owner-to-view projection with
an explicit supported-observation interpretation. Reading through that
observation checks its owner support; it cannot satisfy a transferable view
requirement without the checked lending transition.

A borrowed composite's observations retain loan identity and scope access.
Projection, fold, unfold, `open`, `close`, exact-resource normalization,
symbolic range splitting, and callback-fact extraction must preserve that
dependency. Identical descriptions may share storage, but descriptions
from different scopes cannot be merged by dropping one scope's conditions.
Combining an owner and a live borrowed description cannot absorb the loan.

There are three different proof outcomes:

- A copied scalar value or a proposition about an explicitly recorded old
  snapshot may remain true after a loan ends.
- A claim that the *current* cell still has that value requires checked
  framing from that snapshot, using active support or a proved disjoint
  effect. A later overlapping write blocks that transport.
- Permission to load the current cell requires current usable authority.
  Neither of the preceding propositions creates it.

Audit `CResourceComposition` and remembered premises as well as explicit
resource entries. A theorem about an old resource context can be retained
as historical evidence; it cannot reinstall a consumed access token,
authorize a current store, or manufacture a scope-close transition.

For stable facts in resource bodies, extend the current memory-coverage
validator only after the kernel carries support dependencies through every
resource operation. A schematic body containing `views p[0..1]` and
`fact p[0] == 0` may be folded while its access is active. Its hidden support
bundle must keep the required access or opening obligation. It cannot export
an apparently unscoped resource containing that fact and then let the lender
recover the bytes. No theorem may erase the bundle.

Static validation establishes that the declared footprint can cover the
fact. Dynamic folding also proves the fact, valid current access, and
dependency capture. Static coverage alone does not justify the assertion.
Track dependencies reached through nested resources and predicate definitions;
retain existing guard/bounds checks and bounded explicit unfolding behavior.

### D8. Function entry, call planning, and return

Ordinary function-body certification starts from a generic contract context.
Its input views receive an abstract shared access environment with externally
supplied backing, not secretly invented ownership of external memory. The
proof must work for any caller satisfying that environment. It cannot close
an external scope or recover its lender's resource. Equal/overlapping view
arguments remain valid instantiations; distinct binder names are not a
separation premise.

Use one hidden callee access scope for the input-view environment. Each
view clause selects a description in it; several descriptions can use the
same available access capability in one sequential context. Never mint a
separate full live token for each formal parameter and later identify those
tokens when the actual pointers alias.

The caller constructs this environment with backing entries of two kinds:
newly lent owned pieces, and shared reborrows of existing loans. A shared
reborrow pins a selected parent access share as a dependency of the fresh
call scope. Several clauses using the same parent capability share that
dependency; different parent scopes remain separately recorded. The callee
gets access to the fresh scope, while the caller retains its close right.
Closing that scope returns the pinned parent shares and enables recovery
only for newly lent owned pieces. It never closes the parent scopes.

This is the default calling convention, including nested readers. It makes
generic function certification independent of whether its caller supplied
owners, one outer loan, or several outer loans. Projected child backing is
checked at creation against the parent's frozen footprint and generation.
Read checks use the child record directly; closure obligations maintain the
parent protection without walking the full ancestor chain at every load.

Prepare calls in a checked two-phase operation:

1. Instantiate the interface and evaluate addresses, bounds, model arguments,
   and dependent loads in the prescribed entry snapshot. Record the actual
   support for every such load.
2. Plan the required owned transfers, consumes, and shared loans jointly.
   Check coverage, resource quantities, cross-clause conflicts, and any
   explicitly proved conditional partition. A preliminary read during
   planning does not lend or duplicate the resource.
3. Check the complete plan and atomically publish the caller residual,
   suspended escrow, callee capabilities, scope bindings, and frame evidence.
   Keep the plan separate from authority until its obligations are discharged.
4. Execute/apply the callee rule. Its write/havoc footprint comes from the
   checked transferred authority. Reentrant calls see only authority their
   own contracts actually supply; saved caller owners do not become usable.
5. At each returning path, check returned owned/consumed/produced resources,
   restore callee-held access shares, close scopes created for this call,
   recover their escrows, and check packaging/postcondition transport.

The exact ordering of postcondition evaluation must respect the current
entry/post metadata: callee postconditions are checked before dropping access
needed to interpret them; only justified facts are transported to the caller.
Validate all return obligations before committing caller recovery. A failed
callee result cannot leave a recovered owner beside live access.

When satisfying a view from an existing view, split/hold access from its
existing backing under the child dependency and return it when the child
scope closes. A fresh child scope is justified by that held parent authority;
it is not a new independent source of memory access. Keep the dependency
graph acyclic by construction. Directly forwarding the same scope can be a
later checked optimization, but is not required and must preserve the same
call extent, interface interpretation, and return obligations.

The roles in the normalized resource specification remain distinct:

| Interface item | Boundary treatment |
| --- | --- |
| Borrowed ownership (`owns`) | Move usable ownership into callee, return the promised resource on return; this is not a shared loan. |
| Borrowed view (`views`) | Lend from ownership or pass existing scoped read authority; no independent owner remains usable. |
| Consumed resource | Transfer the selected resource with no automatic recovery promise. |
| Produced resource | Require checked output authority and composition with the caller frame; cannot mint a live access share. |
| View in an output or packaged output | Preserve an explicitly existing outer dependency, or reject an escaping loan that the supported interface cannot express. |

Do not interpret every ensured `View` as a new persistent capability.
Implicit return of a call's own input view normally gives back the access
share and closes the call-created loan. Conversely, blanket deduplication
against a caller owner is no longer a valid way to discharge obligations.
Before accepting any explicit view-producing form, classify where its live
authority comes from. Unsupported escaping-borrow contracts get a source
diagnostic; merely rejecting a valid returned raw C pointer is incorrect.

### D9. Callbacks, refinement, effects, and non-return

Direct verified calls, named function contracts, indirect callbacks, explicit
execution theorems, automatic contract formation, and certification must
share the same transition boundary. A named contract's body-independent
interface cannot assume hidden resource availability from its original
concrete function.

Refinement must account for resource transformations, not just compare
`Own` and `View` variants. An implementation verified with a view can serve
an interface that gives ownership if a checked adapter lends and recovers it.
An implementation that requires a writer cannot serve an interface offering
only a stable view. Check callback execution and refinement on concrete live
callers; a proof under an inconsistent precondition is not a bad-call test.

The exact function-pointer `Contract(p)` evidence retains its supporting
table cell/resource generation. An active view of that supporting cell
prevents mutation; an ordinary owner-supported observation is invalidated by
an allowed mutation. Stable views must not accidentally make all callback
facts permanent. Preserve the real rbtree callback footprint regressions.

Memory-effect summaries are consequences of the transferred authority.
They cannot widen it. Audit direct stores, abstract call havoc, loop havoc,
allocation effects, and trusted external contracts. External specifications
remain explicit trust assumptions, but their declared effects must still
compose with the caller's loans. An unknown implementation is not permission
to ignore a frozen range.

Every normal and early return uses the same discharge rules. A non-returning
path does not synthesize a returning owner; a partial-correctness proof may
retain an unclosed loan on that path without pretending recovery occurred.
Keep termination proof obligations separate. Unsupported exceptional exits,
longjmp, and future C++ unwinding need explicit lifetime transitions later;
do not assume cleanup occurred because a source block or proof task ended.

### D10. Stack storage, heap storage, and object lifetime

The current caller-local view shortcut must become checked lending from
implicit local authority. Ordinary C users still need no resource clause
for each local array. Materialize or identify the local's authority internally,
tie it to the local allocation generation, and suspend the selected bytes
when lent. Direct local assignment, indirect aliases, initializer paths,
aggregate writes, and loop/call havoc must consult the same suspension state.

Do not implement this solely by denying external stores. A local's block
prefix is not evidence that the current component may write it. Likewise,
free checking only for visible `View` entries misses descriptions stored
inside resources or held by another context. Allocation lifetime checks must
use active loan/backing evidence, including loans of subranges.

For heap operations retain the existing allocation token, size, initialized
state, and pointer checks. A live subrange loan prevents free and any realloc
operation capable of invalidating that allocation, even if the allocator
might fail or return the same address. After scope closure/recovery, the
existing legal operations succeed. A recycled address has a fresh allocation
identity and cannot revive an old descriptor. Ending access also does not
allow a later recovery to resurrect an already-ended object: destruction
must discharge or explicitly consume pending escrow/restoration obligations,
and recovery checks the still-valid allocation generation. Ordinary P1
call return recovers before local lifetime teardown.

Owning raw storage and viewing it does not certify a typed initialized value.
Keep existing initialization checks at reads; P1 is not adding Rust's typed
validity rules. Globals, static storage, and literal storage retain their
existing lifetime and mutability classifications while using the same access
checks where applicable. A compiler-certified immutable literal may have
permanent read support; it is not a general way to give mutable memory an
unbounded loan.

### D11. Loops, proof branches, and hidden dependencies

An outer function's input view stays active through its loops. A loop that
narrows the body to read access over surrounding ownership needs either
an owner-supported read projection constrained by the body's checked effects,
or an actual scoped loan if it transfers independent read access. It cannot
create a stable view and retain a usable overlapping writer in the body.
Audit `loop_body_resource_context`'s current automatic viewed forms.

Initially scope new temporary loans inside one iteration/call and close them
before the backedge. Outer loans may cross the loop if the invariant carries
their exact authority/dependencies. The backedge must preserve that state;
the invariant cannot existentially forget a leaked share and recreate a full
one on the next iteration. More general changing loan populations require
an explicit conservation invariant and are outside implicit inference.

Treat proof branch cloning as alternatives. Each returning branch must
discharge its own scopes or present compatible surviving obligations.
If one branch ends an outer loan and another retains it, do not union their
resources or unconditionally choose the recovered owner. Keep separate
continuations where needed, or require a checked reconciliation before the
join. Ended branch-local scopes can disappear after proper discharge.

The same rules apply to hidden obligations in folded resources, opened
populations, instance-field scopes, witnesses, and pending proof rewrites.
Resource equality at a join includes the relevant capability/dependency
delta, not only the visible `owns`/`views` list. Use persistent ancestry
and changed-entry indexes; a join must not rewalk the full proof history.

### D12. Sharing families and later Rust interpretation

Ordinary structural resources can share their checked stable body. Their
owned memory becomes borrowed memory under the same protection; observing
them must not reveal owned children. Abstract token lending suspends the
selected token's consumption while the view is active. Other counted units
may remain available. A field-bearing exclusive instance remains unviewable
unless a separately checked sharing interpretation is introduced.

For counted composites, preserve the existing distinction between population
quantity and its population-wide body. Lending a unit must not instantiate
a second independently owned body. A view of that body keeps its actual
memory and resource-state dependencies stable. If consuming another unit
would change a fact advertised by the borrowed body, that transition needs
an appropriate protocol or must wait for the borrow to end. The simple
bodyless-token case may keep its remaining units usable; do not generalize
that behavior to every population invariant. Track pure-looking facts that
depend on resource counts/generations as carefully as memory-dependent facts.

Keep a family sharing operation distinct from a persistent core operation.
Some abstract families may expose facts that remain true through mutation.
That does not make their protected payload an ordinary stable memory view.
Unsupported sharing fails explicitly; never recursively expose arbitrary
owned bytes just because a handle is copyable.

The concurrency model's mutex has a stable shared protocol handle, an
invariant owning its payload while unlocked, and one exclusive guard after
acquisition. Release returns the payload and invariant facts. No raw payload
view follows from the handle. The model's thread-local mutable cell allows
its chosen sequential protocol but refuses transfer to another context.
This is a check of abstraction boundaries, not a production mutex/Cell API.

The Rust correspondence remains deliberately partial. Shared references
require more than pointer constness; exclusive reborrows also restrict
conflicting parent reads and require access-origin reasoning. Rust's
`UnsafeCell` permits a particular interior-mutation interpretation without
removing the need to prevent data races. Rust's exact unsafe alias rules are
not a settled complete model. See the
[Rust Reference](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)
and [UnsafeCell documentation](https://doc.rust-lang.org/std/cell/struct.UnsafeCell.html).
Do not impose these source-language alias constraints on ordinary C pointers.

For model-only exclusive reborrowing, move parent usable authority into a
child and suspend conflicting parent access. A shared child permits shared
reads, while an exclusive child excludes conflicting parent reads and writes.
End the child with its returned authority before enabling the parent. For a
returned field loan, preserve the parent recovery dependency across function
return and recover the field's updated state, not a saved pre-mutation value.
Scope inclusion, access provenance, C storage lifetime, and language reference
validity are separate relationships; a single lexical stack cannot represent
all of them.

### D13. Certificates, diagnostics, and complexity

Add kernel-checked loan transitions to the existing proof object/evidence
path. Evidence must establish the actual predecessor's available capabilities,
the resource selection and side conditions, the exact consumed/produced
delta, and the successor. A surface-supplied after-state, resource hash, or
fresh-looking integer is not sufficient. All normal proof paths must check
the same rules.

Keep access checks and transition checking deterministic. Smart tactics may
find a partition or restoration proof, but the expanded simple proof must
name enough evidence to check it with bounded local work. Ordinary call
syntax may keep compiler-inserted scope mechanics implicit if the call's
checked certificate records them and audit exposes the relationship.

Examples of required diagnostic content, not exact output spelling:

- A store conflicts with the view of `node->next` lent to `inspect`;
  name the loan origin and the attempted write range.
- Call clause 2 requires ownership overlapping the stable view in clause 1;
  report proven overlap or the unresolved separation obligation.
- Scope closure is missing a particular access share or open-resource
  obligation; point to the call/open that retained it.
- A descriptor belongs to an ended scope, or recovery has already consumed
  the entitlement; name the original loan.
- An output tries to retain a loan past the supported call boundary; explain
  the missing lifetime relationship, without silently upgrading permissions.

Use existing bounded diagnostics, structured refusal categories, source maps,
and provenance. Do not print every loan, memory snapshot, or resource in the
project. For unknown aliasing say that separation is unproved; do not report
a known data race.

Index active shares/loans/support by semantic ID, memory by allocation/range,
and reverse dependencies by their immediate parent. Persistent cloning is
constant/logarithmic; a fixed read, split, join, or single-loan recovery
does not visit unrelated entries. Do not add per-store scans of all loans,
eager pairwise reader/writer constraints, or complete-state hash keys.
Reuse the current range evidence/indexing, improving affected fallbacks
when necessary rather than claiming they are already scalable.

Retain checked local proof evidence when symbolic overlap needs explicit
reasoning. The simple checker verifies named coverage/separation witnesses;
it does not search the entire resource context for a favorable partition.
Closing many explicit loans or folding many declared body members may cost
their output size. Repeated fixed-size calls must not accumulate a historical
scan through dead loans. Instrument token-tree bookkeeping as well as memory
and resource operations.

The four-size scaling gates below implement the existing
[verification efficiency contract](../docs/internals/verification-efficiency.md).
Tests must count the work being protected: moving an uncounted scan outside
an instrumented closure is not an optimization.

### D14. Worked traces for implementers

These traces are design notation. They pin the meaning of the hidden call
operations without introducing Surface Click syntax.

**One reader followed by mutation.** The caller starts with Own(x), allocation
generation g, and value 0. It begins k, retains Close(k), and lends Own(x)
into escrow e. The callee receives View(k, e, x) and the root access
capability. The caller's saved frame has Recover(e), but no usable Own(x).
The callee reads 0 and returns the root. The checked return validates its
guarantees, closes k, consumes Recover(e), and reinstalls Own(x). The caller
can now store 1. The scalar result 0 remains valid; a retained description
cannot load x through k, and its old value fact cannot assert that current
x is still 0.

**Two aliased view parameters and a nested reader.** A caller owning x calls
read_twice(p, q) with p == q == &x. One escrow backs two descriptions; the
callee need not own two shares merely to read through two aliases in its
single sequential context. To invoke a nested reader it splits its access
leaf, pins one child under a fresh nested call scope, and retains the other.
The nested reader uses that new scope's description and access. Its return
closes the nested scope and releases the pinned parent child; exact sibling
join restores the outer leaf. The outer return gives the caller its root.
A parallel version would require the
explicit two-context partition that R27 models, not cloning this state.

**Folded cell, viewed link, mutable value.** The caller owns cell(n), whose
body owns n->next and n->value. It wants a setter with views n->next and owns
n->value. The plan checks the body and field separation, suspends independent
use of the parent head, lends the next field, and transfers value ownership.
The setter may write value but not next. Return recovers next and receives
the updated value field. Refolding cell checks the resulting body's facts;
if a model index records the value, its post-call index must be updated by
the contract/proof. The pre-call parent cannot silently retain an obsolete
value fact.

**Borrowed fact hidden in a resource.** A reader has View(k, x), one access
leaf, and evidence that x == 0. It folds a scoped zero-cell resource. Folding
captures the dependency bundle; it does not manufacture an unscoped timeless
assertion. Opening that bundle re-exposes only borrowed access with the same
dependency. Scope end cannot discard the bundle's live access obligation.
Unfolding/closing and returning its share allows normal recovery. A copied
old snapshot proposition may remain, but no current-memory promise escapes.

**Loan ending on only one branch.** Both alternatives start from the same
caller resource state. The true branch can return all of its access and
recover; the false branch can retain its share. These are alternative
states, not pieces to add together. A common continuation cannot receive
unconditional ownership unless both alternatives prove it. If the false
branch first returns its access and recovers too, the checked join can
reconcile the owned result without merging historical scope identities.

## Regression catalogue

The IDs below are stable handoff names. They describe new paired tests to
write, not tests claimed to exist today. Keep current positive fixtures as
inputs. Add a rejecting case that reaches the intended authority check;
an earlier parser error, missing allocation, or unrelated proof failure is
not coverage. Use real allocated live callers for overlap/free negatives.
Prefer explicit simple proofs for the semantic core.

| ID | Positive witness | Required rejection or preservation check | Minimum layer |
| --- | --- | --- | --- |
| R01 | Lend one initialized cell, read it, close, recover, write | Same-value write while access is active fails | Kernel and C call |
| R02 | Two readers share one backing and return both shares | Close/recover with one missing share fails | Kernel/model |
| R03 | Split a leaf, return exact siblings, join | Duplicate leaf, wrong sibling, wrong scope, and ancestor/descendant compositions fail | Kernel |
| R04 | Copy descriptors freely during a loan | Old descriptor fails after end and after another scope starts | Kernel |
| R05 | Recovery once restores the selected ownership | Double recovery and recovery from only an old composition premise fail | Kernel/certificate |
| R06 | Two aliased read parameters and nested readers verify | Reader cannot return outer authority as a new owner | C and kernel |
| R07 | Owned alias probe reads and writes through equal pointers | A concrete caller cannot supply overlapping independent owned/viewed clauses | C |
| R08 | View one field/subrange and mutate the disjoint remainder | Bytewise overlap, even with different element widths, fails | C/kernel |
| R09 | Read-call on a heap object, then free | Free/realloc of a live allocation while any nonempty subrange is lent fails | C/kernel |
| R10 | Call a reader of a local array with no explicit local clause | Direct local/alias store, initializer overwrite, or lifetime end bypassing suspension fails | C/kernel |
| R11 | View a pointer cell and separately authorize a pointee | Pointer-cell view alone cannot authorize pointee access; entry-selected footprint does not retarget | C/kernel |
| R12 | Preserve a snapshot fact, recover, then write a different value | Old fact cannot become a current load/value claim or restore an access token | C/certificate |
| R13 | Observe an owned composite, unfold, legally mutate, refold | Observation does not permanently freeze the owner; old supported facts invalidate | C/kernel |
| R14 | Read through a viewed nested composite | Open/unfold cannot expose write ownership or drop the loan dependency | C/kernel |
| R15 | Fold a resource whose fact is covered by a stable view | Missing access, uncovered read, false fact, and hidden escaping lifetime fail | C/kernel |
| R16 | Open and close a borrowed body with access retained | End scope while body/opening is outstanding fails | Kernel and resource proof |
| R17 | Loan a selected token unit, recover, consume it | Consume lent unit or duplicate its quantity while lent fails; other units remain usable | Kernel/C |
| R18 | Direct, named, indirect, execution-theorem, and certification routes agree | Missing loan obligation or view-to-writer refinement fails on every route | C/kernel |
| R19 | View-based implementation serves an owned interface via a checked loan adapter | Owned implementation cannot satisfy view-only interface | Contract refinement |
| R20 | Reentrant callback reads a lent cell | Callback/hidden-state write to the cell fails; disjoint callback mutation succeeds | C |
| R21 | Stable viewed table cell supports callback evidence | Allowed mutation of owner-supported table cell invalidates old callback evidence | C |
| R22 | Both branches finish their own loans and recover | One-sided closure cannot produce unconditional ownership after join | Kernel/C |
| R23 | Loop retains an outer view and closes per-iteration reader calls | Backedge cannot discard a live share or regenerate a full root; loop havoc cannot write frozen bytes | C/kernel |
| R24 | Early return discharges call-created loans | Return cannot recover caller-owned field while a returned model loan remains live | C/model |
| R25 | Caller result/sidecar proof survives supported packaging changes | Equal resource term after consume/recreate does not revive old support generation | Kernel/resource proof |
| R26 | Ordinary verifier, expand/reverify, profile, and audit agree | Tampered loan ID, range, predecessor, share, scope-end, and recovery evidence fail kernel checking | Certificate/engine |
| R27 | Contexts own disjoint ranges and each writes its range | A reader in one context excludes an overlapping writer/free in the other | Model with kernel-mapped rules |
| R28 | Exclusive parent lends shared child, then exclusive child, and recovers | Conflicting parent writes fail for shared child; parent reads/writes fail for exclusive child | Model |
| R29 | Returned child loan updates caller field and ends later | Parent recovery waits for child and restores updated field state | Model |
| R30 | Mutex handles acquire/release one guard; local cell works within its home context | Unguarded payload access, duplicate guards, and cross-context local-cell transfer fail | Model |
| R31 | Empty view grants no bytes; initialized ordinary read succeeds | Empty view cannot load or prove nonnull; uninitialized read remains rejected | Kernel/C |
| R32 | All share/loan operations remain local with unrelated frame state | Four-size deterministic curves expose ambient scans, history growth, and deep token arithmetic | Kernel/surface scaling |

Start from these existing files rather than inventing a new proof vocabulary:

- R06/R07: [alias-owned.click](../design/borrow-probes/alias-owned.click),
  [alias.c](../design/borrow-probes/alias.c), and
  [alias_and_cleanup.cpp](../design/borrow-probes/alias_and_cleanup.cpp).
  The C++ file is compiler/model evidence only in this issue.
- R08/R13: [field-split.click](../design/borrow-probes/field-split.click) and
  [composite_piece_caller_frames_viewed_field.md](../mdtests/composite_piece_caller_frames_viewed_field.md).
  The latter's existing overlapping contract needs a sidecar migration.
- R09: [heap_scoped_borrow_then_free.md](../mdtests/heap_scoped_borrow_then_free.md).
  The existing [heap_free_rejects_borrowed_access.md](../mdtests/heap_free_rejects_borrowed_access.md)
  rejects missing live-allocation evidence; it does not by itself test
  free with a valid allocation token and a still-live loan.
- R10/R31: [borrowed_local_view_in_bounds.md](../mdtests/borrowed_local_view_in_bounds.md)
  and [borrowed_local_view_bounds_rejected.md](../mdtests/borrowed_local_view_bounds_rejected.md).
- R18/R21: [rb_augment_callbacks_helper_owns.md](../mdtests/rb_augment_callbacks_helper_owns.md),
  [rb_augment_callbacks_helper_owns_rejects_unseparated.md](../mdtests/rb_augment_callbacks_helper_owns_rejects_unseparated.md),
  and [opaque_call_does_not_preserve_overlapping_field.md](../mdtests/opaque_call_does_not_preserve_overlapping_field.md).

For R32, vary sizes 16, 32, 64, and 128 independently for live loans,
unrelated resources, completed sequential loans, reader nesting, and
split-tree depth. Add a selected folded resource with increasing unrelated
definitions. Separate construction cost, operation cost, and total repeated
workflow cost. The fixed operation should be independent of unrelated
entries except indexing; explicit n-operation workflows should follow the
documented near-linear bound. Compare counted work against those bounds,
not a large fixed threshold chosen after looking at timings. Include a
validity check so an early failure cannot masquerade as good scaling.


## Implementation record

Cards V0-V17 landed on the codex coordinator branch during 2026-09-12 and
2026-09-13 and were rebased onto master on 2026-09-13. Commit subjects are
the stable identifiers; the dated checkpoint prose is in this file's git
history. Doc-only "Record ..." commits are omitted.

| Card | Landed as | Established |
| --- | --- | --- |
| V0-V6 | Build stable view loan semantics spine | Baseline inventory (201 files with executable `views`); executable model in `loan_model_tests.rs` with bounded search to depth five under a 50,000-state cap and per-transition inductive facts; `loans.rs` ledger with fresh identities, persistent AVL snapshots, structural evidence seals, `OwnedResourceObservation` distinct from `StableViewDescription`, and the body-independent joint planner (exclusive requirements first, disjoint range splits, one backing per identical or overlapping view, transactional rejection, exact recovery recipe). |
| V7 | Add loan ledger state identity; Preserve loan identity in CState plumbing; Bound stable view loans to backing and checked state; Opt in direct calls to stable view planner; Reconcile checked loan call recovery; Preserve loan participant identity in CState; Complete candidate stable-view call recovery; Add checked nested stable-view reborrows; Preserve nested view binding identity; Exercise nested stable view body calls; Complete candidate stable-view call outputs; Retain checked loan call evidence across V7 paths; Reconcile loan evidence with output and write checks; Keep stable view certificates opt in | Ledger, participant, and occurrence bindings in `CState`; direct body and verified calls through the planner; nested reborrows with exact output-view ancestry; canonical parent recovered only after return obligations; bounded persistent entry/recovery evidence for certification. Legacy verification stays outside the opt-in path. |
| V8 | Route candidate verification and refinement through checked views; Check stable view refinement subranges; Stage loan-aware refinement behind candidate mode | Owned-interface to viewed-implementation refinement, including proper subranges; the reverse is refused; named and indirect callbacks converge on the common verified-call preparation. |
| V9 | Enforce active stable loan memory footprints; Clean up active loan index checks | Persistent interval indexes for active concrete memory loans; every supported write and lifetime-ending path checks them; unsupported symbolic overlap fails closed; ending a child restores parent protection. |
| V10 | Preserve stable view loans through control flow | Loan evidence through sequential statements, proof transitions, terminal outcomes, loop preservation candidates, `break`, and compatible branch joins; loop effect summaries check loan footprints before havoc; branch abstraction preserves loan-covered cells. |
| V11a | Preserve loan dependencies through resource rewrites | One canonical persistent loan-dependency root per resource occurrence, shared with `CState` in constant time; fold, unfold, observe, expansion, and checked rewrites preserve exact dependencies or refuse ambiguous equal occurrences, mixed bound/unbound children, and laundering into owned heads. |
| V11b | Decompose composite stable view loans | A view of a folded composite is an atomic restoration group: head removed from usable authority, decidable body reduced to owned primitive memory and token pieces, recovery restores the head only after the whole share tree closes. Refuses instance children, unresolved nested frontiers, viewed children, and fact-bearing bodies; `LoanLedger::lend` still refuses `Composite` and `Instance`. |
| V12 | Allow current views to cover resource facts; Capture dynamic stable-view fact dependencies; Close stable view fact dependency gaps | Static coverage by properly scoped views; proof-time observe/unfold/fold collect every current-memory load and require the exact live binding; traversal through integer, algebraic, sequence, conversion, and opaque carriers, failing closed on opaque ones; byte widths preserved. |
| V13 | Route stable view mode through surface verification; Reuse stable proof entry state for certification; Remove unvalidated external root prototype; Update V13 documentation and migrated diagnostic; Refresh stable view corpus inventory | `ViewSemanticsMode`; the five `stable_view_*` fixtures; the durable output inventory in `docs/internals/view-output-inventory.md`. The unvalidated external-root prototype was removed before integration. |
| V14 | test: extend V14 loan models; docs: record V14 model handoff assumptions | Model-only two-context partition/transfer, shared readers across contexts, shared and exclusive reborrows, returned-field transport, mutex invariant/guard, thread-local confinement; representative operations compared with the production ledger. Scheduling, atomics, Rust rules, production reborrows, and thread APIs stay model-only. |
| V15 | Add semantic identity at verification boundary; Add structured stable-view loan diagnostics | Artifacts bound to source inputs, target/profile, resource-semantics version, and view mode; legacy artifacts have absent identity. Refusals carry category, operation, bounded subject, identifiers, and origin; proven overlap is distinguished from unproved separation. |
| V16 | Enforce local scaling for loan evidence and views; Strengthen V16 scaling evidence | Incrementally checked persistent evidence summaries; ordered interval clustering; resource subtraction indexed by memory start; four-size curves for live state versus completed calls, active intervals, split/read/join depth, persistent edits, dependency changes, certificate deltas, unrelated resources, and overlap chains; persistent-tree work accounting. |
| V17 (partial) | Narrow stable callback view footprint; Migrate composite and loop view contracts | The rbtree callback contract narrowed to the exact shared cell range it reads; redundant view requirements removed from composite, population, and loop contracts; inventory 200/345 to 198/337; the last batch (Migrate remaining stable-view contract overlaps: `bounded_pool.click`, `modular_call_requirement_indexes_footprint`, `opaque_calls_preserve_separated_field`) was recovered from a codex side branch on 2026-09-13 and passes its focused mdtests and example. Open: top-level reader fixtures wait on the borrowed-input root. |
| V18 (partial) | Reject cross-arena reborrow borrowers; Preserve stable-view authority across proof rebases | Reborrow validates both participants against the ledger arena when issued and when applied; proof-entry and execution-evidence rebases require identical ledger, participant, and binding authority; resource-empty nested function and named-contract bindings preserve an active outer loan. |

Gate evidence: the codex coordinator's authoritative `scripts/check.sh` run
at its final integrated commit passed 2,951 tests and all four fixture
gates. After the rebase onto master (upstream had moved by 38 commits,
including "Permit a read through either spelling of an aliased pointer"),
the same script passed on the rebased tip on 2026-09-13 with 2,959
library/binary/documentation tests and all four fixture gates.

## Working agreements

### Assignment and integration

Assign one card at a time to a Luna agent. Each task prompt should contain:
the integrated starting commit, this file and its D/R sections, the selected
card, its predecessor handoffs, the file ownership boundary, and the shared
completion checklist below. The agent should not have to reconstruct intent
from this conversation. Do not assign a card until its dependencies have
landed and their APIs/tests exist.

The table gives a recommended default order. Some adapters can be developed
independently after the common API is fixed, but most touch shared kernel
files. Start sequentially. Parallel assignments require disjoint file
ownership established by the coordinator; the table is not permission for
several agents to edit `functions.rs` or `resource_algebra.rs` at once.

| Card | Deliverable | Depends on |
| --- | --- | --- |
| V0 | Fresh baseline, fixture classification, authority-path inventory | None |
| V1 | Small transition model, preservation arguments, reviewed API contract | V0 |
| V2 | Scope identities, conserved share tree, persistent ledger | V1 |
| V3 | Memory/token lending, escrow, projection, and recovery | V2 |
| V4 | Kernel proof transitions and hostile certificate tests | V3 |
| V5 | Owner-supported observations separated from borrowed access | V4 |
| V6 | Joint checked call-resource planner | V5 |
| V7 | Direct-call input/return binding and scoped recovery | V6 |
| V8 | Named contracts, callbacks, and refinement integration | V7 |
| V9 | Implicit local authority and heap/lifetime enforcement | V7 |
| V10 | Loop invariants, effects, branches, and early returns | V8, V9 |
| V11 | Composite/population opening and dependency preservation | V5, V7, V10 |
| V12 | Stable viewed facts and guarded coverage | V11 |
| V13 | Small C contract migrations and explicit-view outputs audit | V8, V9, V12 |
| V14 | Model checks for threads, mutable reborrows, and protocols | V4, V11 |
| V15 | Expansion, audit, refusal diagnostics, and import/proof identity | V8, V10, V12 |
| V16 | Deterministic complexity gates and local fixes | V10, V11, V15 |
| V17 | Full corpus/rbtree contract migration and compatibility record | V13, V15, V16 |
| V18 | Independent adversarial review and production-readiness gate (step 6 under remaining work) | V14, V17 |
| V19 | Default semantics cutover, documentation, final cleanup (step 8 under remaining work, after the step 7 escaping borrows) | V18 |

Common completion checklist for every implementation card:

1. Work in an isolated task branch/worktree from the assigned integrated
   base. Read applicable AGENTS instructions and the current predecessor
   handoff. Inspect symbols before assuming the planning map still matches.
2. Implement only the card's boundary. Add meaningful paired positive and
   negative tests and the deterministic work checks relevant to new hot
   paths. Preserve original C bytes in existing fixtures and examples.
3. Use the shared bounded verification engine. A prompt ordinary proof
   failure may be repaired with appropriate proof steps; tooling slowdown,
   unverifiable expansion, or unusable diagnostics must be reduced and fixed
   before proceeding. Do not increase limits or quarantine coverage.
4. Run focused tests, then the unfiltered `scripts/check.sh` and judge its
   exit status. Do not commit a failing placeholder test or merge an
   incomplete prototype. Report a blocker and a small intended regression
   if it cannot be resolved inside the card; do not create another issue
   without user authorization.
5. Leave a concise handoff in the task result: commit/base, exact APIs and
   invariants added, R IDs covered, test commands and exit statuses, whether
   production behavior changed, remaining limitations, and anything the next
   card must use or must not rely on.
6. The coordinator checks the diff, coherent scope, primary cleanliness/base,
   and relevant/full gates before Git integration. If the base moved, rebase
   and rerun affected checks. Downstream work starts from that tested commit.

Focused command patterns, with filters chosen for the card's actual tests:

    cargo nextest run --lib resource_tests
    MDTEST_FILTER=borrowed_local_view cargo nextest run --test mdtests --no-capture
    scripts/check.sh

These focused commands are examples, not substitutes for the gate. If new
modules/test names differ, report the real filters. Record the verifier
process tree as exited after an interrupted or timed-out run before trusting
subsequent timings.

Use this future assignment template after implementation is authorized:

    Implement card V__ of issues/fix-views.md from integrated commit ____.
    Read design sections D__ and regressions R__ plus predecessor handoff ____.
    Your file boundary is ____. The common API is the one in commit ____.
    Preserve existing C source. Do not implement successor cards or redesign
    the loan protocol. Complete the card's tests and scripts/check.sh.
    Return a tested commit and the handoff below; report any concrete blocker.

Handoff template:

    Card and base:
    Commit:
    Production behavior changed? If so, exactly how:
    Checked APIs / invariants added:
    R IDs -> actual test names and verification layer:
    Commands -> exit statuses:
    Scaling evidence, if applicable:
    Temporary adapters and required removal:
    Remaining limitations / next card inputs:

If a card reveals more than one independent architectural change, its agent
should return a proposed smaller boundary before expanding scope. The
coordinator can split the card into named subtasks in this same issue with
the same laws/regression IDs. A Luna task should finish one reviewable
transition or integration boundary, not silently become the entire refactor.

### Staging without an unsafe partial cutover

V2-V4 can land checked APIs and kernel tests without changing how ordinary
source contracts are interpreted. V5-V17 then route proposed stable-view
inputs through the same checked engine in focused tests, while existing
contracts are migrated. Any state containing a real loan must obey all of
its access rules; an adapter may not silently fall back to old view behavior
for an unsupported operation.

If a temporary input-interpretation selector is needed, keep it internal to
tests and the coordinated rollout, with explicit semantic identity. It may
choose how entry contracts are instantiated; it must not skip checking or
select a second verifier. Scope-bearing states and certificates cannot be
consumed by an old rule that ignores their obligations. Never cache or
certify an old-interpretation result as a stable-view result.

Keep the existing public behavior unchanged until the complete path and
corpus are ready, and keep this issue open. The candidate path must cover
ordinary verify/expand/profile/audit, not a hidden stand-alone checker.
Step 6 requires the full corpus under the candidate interpretation with no
uncovered fallback. Step 8 enables it by default and removes temporary selectors,
legacy independent-memory-view construction, and obsolete tests/docs.
No permanent dual semantics or public compatibility switch is part of P1.

At V1, pin the precise staging seam and removal list using the actual engine
APIs. If isolating the candidate interpretation would require a second
checker or broad pervasive flags, stop that approach: keep the dependent
adapter changes in a coordinated integration worktree and integrate one
coherent tested cutover commit. Do not make a Luna agent invent a migration
architecture mid-card or merge a half-enforced semantic change to stay green.


## Concurrency and Rust design checks

Build a small checked resource-transition model for the matrix below before
adding a production threading or Rust frontend. Include memory steps and
context splitting: asserting flags on a proposed loan struct is not evidence
that resource composition prevents races. Each step must preserve the rights
held in the other context. [Iris, frame-preserving updates](https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf)

Exercise an exclusive parent loan with a shared child and an exclusive child.
The latter must suspend conflicting parent reads as well as writes. Include
a borrow returned into a caller-owned field and recovery of that field's
updated value. Keep access-origin checks, source reference types, object
lifetime, and loan expiration distinct. The compiler evidence and detailed
C++/Rust interpretation now live in
[Supporting more languages](../design/supporting-more-languages.md#borrowing-complications-to-revisit-for-rust).
The existing probes remain regression inputs for this issue's model.

Use one mutex-like protocol as a check on abstraction. Its shared handle
grants the right to acquire a guard; protected memory is owned by the invariant
until acquired, and returned on release. Two handles must not project raw
payload views or duplicate payload ownership. A thread-local mutable cell
needs a different sharing protocol; allowing interior mutation does not
itself justify cross-thread access. Language/library interpretation is
recorded in the shared design document.

Copyability alone must not authorize moving an abstract view to another
thread. Its sharing interpretation must justify that transfer; test a
thread-local cell protocol alongside the transferable mutex handle in the
model. This leaves a place for Rust's type-dependent thread-safety rules.

The first release need not add customizable sharing predicates, Rust trait
checking, or production locks. Keep the family sharing operation separate from
unconditional recursive projection of owned bytes. Unsupported abstract
sharing must fail explicitly. Atomics, ordering, and Linux RCU remain in
[concurrency-and-atomics.md](concurrency-and-atomics.md); a small
release/acquire publication example is a memory-model design check, not a
claim established by stable views or by sequential interleaving alone.

## Intended regressions and acceptance criteria

The smallest semantic regression uses ordinary memory `x` initially 0:

```text
owner lends x into scope k
reader A receives View(k, x), Live(k, 1/2)
reader B receives View(k, x), Live(k, 1/2)
both read 0; lender's store/free/end-scope attempt fails
both return their live shares; end k; recover ownership once
store 1 succeeds; any retained View(k, x) fails to authorize a read
```

This is a proposed kernel/model regression, not supported threaded C syntax.
It must fail under a naive extension of current owner-plus-view composition
and pass under the new checked rules. Also cover:

| Case | Required result |
| --- | --- |
| Call a read helper, then mutate/free | Pass, with automatic scoped recovery. |
| Two aliased read parameters or nested read helpers | Pass without requiring their separation. |
| Store via another alias during a shared loan, including a same-value store | Reject, including through callbacks and stack aliases. |
| View one field while writing a disjoint field | Pass and preserve the viewed value. |
| Branch ends a loan on only one path, or recovery occurs twice | Reject invalid join/recovery; keep valid branch-specific proofs possible. |
| Copy a descriptor, end its scope, start a new scope, then use the old descriptor | Reject stale authority. |
| Fold a view or store it in an abstract resource, then end its scope | No live access/fact may escape without the corresponding scope obligation. |
| Shared or exclusive child reborrow | Parent conflicting accesses fail until child ends; correct authority returns afterward. |
| Returned field loan | Parent recovery waits for the returned loan; mutation is reflected in the recovered state. |
| Two workers own disjoint array ranges | Both may write; shared loan restrictions stay local to the borrowed range. |
| Shared mutex-like handles | Guard acquisition transfers authority; unguarded access and duplicate guards fail in the selected protocol. |

For this P1 issue, thread contexts, Rust-style returned loans, mutable
reborrows, and the mutex protocol may be exercised in the checked model.
The supported C cases must exercise the actual verifier. New production
thread APIs, Rust syntax, and a complete unsafe alias model are not required
to close the issue; the model must explain how those extensions preserve the
implemented shared-loan laws.

For contract-overlap negatives, include a concrete caller with live allocated
memory. Proving a function under an inconsistent `owns`/`views` precondition
does not test rejection of the bad call. Diagnostics must identify the
conflicting loan and range instead of silently treating the input as a valid
borrow or fixing the proof with an unjustified separation assumption.

Acceptance requires:

- V0-V17 and the eight remaining steps have integrated handoffs, all D2 laws
  have enforcing paths, and
  R01-R32 have the required positive/negative evidence at their stated
  layers. Preserve the result map in durable documentation before closure.
- Stable views are the default and sole ordinary-memory interpretation.
  No legacy fallback, temporary rollout selector, stale proof/cache result,
  or alternate verification entrypoint can bypass the checked loan rules.
- The stable ordinary-memory semantics, borrow extent, composition laws,
  recovery, and distinction from owner-supported observations are documented
  and enforced in the kernel. The small model's exact assumptions and its
  relationship to implemented rules are recorded; no claim of a complete Rust
  alias model or C concurrency model is made.
- Calls, callbacks, loops, local memory, resource abstraction, and certificate
  validation share those rules. Representative ordinary verification,
  expansion/reverification, and audit results agree.
- Migration positives and negatives above have focused automated regressions;
  existing C sources remain unchanged. Both read sharing and legitimate
  sequential alias mutation remain expressible without proof-only C changes.
- Deterministic four-size regressions vary loan count, nesting depth, repeated
  read calls, and unrelated resources independently. Loan lookup/closure and
  permission splitting touch the affected loan/dependency delta, with indexing
  overhead, rather than scanning/cloning the whole state or all historical
  view copies. Fraction representation costs must also be bounded by the
  explicit certificate; the initial binary share tree must not hide
  quadratic identity/path handling behind constant-size token names.
- `scripts/check.sh` passes. Update resource docs and affected fixtures when
  semantics land, preserve the implemented design outside this issue, then
  delete this issue and its list entry.

## Coordination

[memory-vs-resources.md](memory-vs-resources.md) remains a P1 refactor preserving
current semantics. Reuse its unified transitions and support provenance;
coordinate representation boundaries now. The efforts may share implementation
work, but stable views must be an explicit, tested semantic change, not an
accidental side effect of unification. This issue owns stable shared-memory
views and their loan protocol; the shared-permission item in
[resource-algebra-extensions.md](resource-algebra-extensions.md) should use
these rules rather than develop a competing meaning of views.

The [basic C++ issue](basic-cpp-support.md) consumes the stable access and
lifetime-transition APIs; its constructor/destructor work must not implement
a second loan ledger. The [goto issue](goto.md) consumes explicit scope-exit
obligations when control flow needs them; completing general goto is not a
prerequisite here. Production threading, atomics, Rust syntax, and arbitrary
escaping-borrow syntax remain outside this issue. Coordinate these boundaries
through [Supporting more languages](../design/supporting-more-languages.md)
and keep rbtree as the launch demo.
