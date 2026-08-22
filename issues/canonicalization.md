# Canonicalize every term at creation

## Violated invariant

Every term in the proof state — in a symbolic value, a fact, a goal, a
resource range, or a lowered proposition — is in canonical form, and that
form is established where the term is created. Canonicalization is one
function with one contract (`canonical_term` and its offset and condition
analogues; see `docs/internals/canonicalization.md`):

- a memory load whose value the snapshot records becomes that value;
- every other memory load becomes its load variable, the kernel variable
  identified by the loaded cell and the snapshot of its last write; and
- arithmetic structure, operand order, and the proof context are never
  consulted, so equality of canonical forms holds by definition.

Every load variable carries a defining fact `v == load(snapshot, pointer)`.
Defining facts are the base of the construction and are the only facts in
which a load term legitimately remains. A consumer never re-inflates a load
variable into its load for comparison; the kernel may view a load variable
as its load for provenance reasoning (the memory derivation DAG), which
needs the snapshot.

Comparison-time canonicalization — the kernel's decision procedures and
replay comparing canonical forms — is a safety net, not something any
consumer depends on. Because terms are canonical when created, changing
what canonicalization does later changes one function, not every comparison
site.

Canonicalization is deterministic and idempotent, and its result does not
depend on whether a term came from symbolic execution, lowering, or contract
evaluation. Every atomic fact emitted by symbolic execution is selectable
and consumable by bounded simple proof steps, and canonicalization and fact
selection stay linear up to the repository's indexing allowances as
unrelated snapshots and facts are added.

## Why this invariant

Symbolic execution produces a new snapshot at every statement, so one
unchanged cell is read through many different load terms over a proof.
Without a creation-time invariant, three things go wrong:

- **Large terms.** A loaded index such as `owner->len` enters the pointer
  `data + len` as a load term, snapshot and all; terms grow with the number
  of snapshots.
- **Facts the kernel knows but a simple proof cannot cite.** In
  `owned_string_push`, after the null-terminator store the kernel records
  `data[len] == 0` using its own term for `len`, while the Surface Click
  `at(statement(4).entry, owner->len)` lowers to a different term for the
  same value. Bounded smart reasoning bridges them; no simple tactic step
  can, because `transport`, `rewrite`, `normalize`, and `assumption` see
  two terms.
- **Consumers that must know which positions are canonical.** When only
  some positions canonicalize, every decision procedure carries its own
  bridging for the others, and enabling canonicalization in one more
  position splits one value into two terms wherever a consumer still
  assumes the old one. This was measured twice (see "Constraints learned").

## Current state

Landed on master (commits `335868c4` through `abdf4180`, 2026-08-20/21):

- `canonical_term` / `canonical_offset_term` / `canonical_condition_fact`
  are the one canonical form, with regressions in
  `src/kernel/tests/canonicalization_tests.rs`.
- Comparison-time canonicalization is complete: the equality graph, affine
  cancellation, the signed-order-bounds index (dual-keyed under the fact's
  endpoint term and its canonical form, entries carrying the fact's own
  term), the exact frame matchers, the memory-resolution equality's deep
  arm, the overflow helpers, `canonical_bound_holds`, and certificate
  evidence for `Int32IncrementStrictlyIncreases` all join by canonical
  form. Surface synthesis resolves load variables through the registry.
- Creation-time canonicalization exists in one position: symbolic
  execution introduces a load variable for a loaded **pointer**
  (`canonicalized_pointer_value_from_int_cell`,
  `canonicalized_symbolic_load_value`).
- Creation-time canonicalization for loaded **indices** entering pointer
  offsets is implemented at the three birth sites (`apply_c_add`,
  `evaluate_spec_pointer_offset_paths`, contract `offset_pointer_by_elements`)
  behind `CLICK_CANONICALIZE_AT_CREATION=1`, off by default; three
  fixtures fail with it on (below).

## Plan

The invariant is established at the four places terms are created —
symbolic execution (values and facts), lowering (Surface Click to kernel
propositions), contract and spec evaluation, and resource fact projection
— together, behind one switch, never position by position.

### Stage 1: measure the distance (done 2026-08-21)

`check_canonical_at_creation` (`src/kernel/eval/memory_loads.rs`), behind
`CLICK_CHECK_CANONICAL_AT_CREATION=1`, compares every condition fact
entering a `PureFactContext` with its canonical form (defining facts
exempt) and reports each distinct (rewrite kind, creating module) once
with an example. Run over both fixture gates:

- Every violation is the same rewrite: a load term whose canonical form
  is a load variable (about 94%) or the value the snapshot records (about
  6%). No other difference between created and canonical terms exists.
- The creating modules are the four creation kinds: symbolic execution
  (`execute_c_statement_verification_paths_with_prefix`,
  `evaluate_c_memory_load_paths`), lowering (`lower_point_proposition`,
  `lower_outcome_proposition_with_program_points`,
  `lower_ensure_proposition_goal`), contract and spec evaluation
  (`c_function_contract_certification_assumptions`,
  `lower_spec_comparison_proposition_at_state`), and resource fact
  projection (`project_resource_context_observable_facts`,
  `append_composite_resource_declared_facts`,
  `evaluate_composite_resource_fact_propositions`,
  `LegacyResourcePureFacts::new`). The many proof-engine frames
  (`claim_proofs`, `replay_engine`, `proof_object`) re-assume facts those
  four created.
- Some snapshot-bridge facts `load(A, p) == load(B, p)` canonicalize to a
  reflexive `v == v`; under the invariant they are redundant and can be
  dropped at creation.

### Stage 2: canonicalize at every creation point, behind one switch (implemented 2026-08-21)

`CLICK_CANONICALIZE_AT_CREATION=1` (`canonicalize_at_creation_enabled`)
makes memory loads evaluate to their load variable where they are born,
so every fact, offset, and range built from them is canonical without
touching the sites that build facts:

- **Resource materialization.** Resource lowering stores each owned or
  viewed cell's value as the load variable for (base snapshot, pointer)
  instead of the load term (`resource_lowering.rs`, `proof/resources.rs`
  via `canonical_load_term`). This was the root of most non-canonical
  facts: a later read of `owner->len` returned the materialized load term
  as the cell's recorded value, never reaching the symbolic-load path.
- **Symbolic execution.** `canonicalized_symbolic_load_value` returns a
  load variable for int and byte loads too, with the defining fact in the
  path's facts. Pointer reinterpretation of a materialized cell accepts a
  load variable and records its defining fact
  (`canonicalized_pointer_value_from_int_cell`).
- **Contract evaluation.** `symbolic_contract_memory_load` returns the
  load variable for int and byte loads, and pointer reinterpretation
  accepts a load variable (`evaluate_contract_memory_load_from_memory`).
- `canonicalized_offset_index_term` remains under the same switch as a
  safety net for indices built from loads created elsewhere.

Two fact shapes are the base of the construction and keep their load
term: defining facts `v == load(snapshot, p)`, and store facts
`load(after, p) == v` where `after` records `v` at `p` (exported from a
certified store record and cited by certificates through
`at(statement(n).exit, ...)`). The stage-1 checker exempts both.

Measured with the switch and the checker on: **zero** creation-time
violations over the lib suite and both fixture corpora. Comparison-time
canonicalization stays on as the safety net. With the switch off the tree
is unchanged and green.

### Stage 3: fix the consumers the switch exposes

With the switch on, the lib suite has 19 failures, 17 of 398 mdtests
fail, and the examples harness stops at `bounded-pool` (an
expansion/replay disagreement). Every failure is a consumer that still
assumes a load term. Characterized so far:

- **Source-site annotation must not move an anchored form.**
  `surface_with_source_site` stripped an operand's existing `at(point, ...)`
  selector and re-anchored it at the new point, so recording a step
  premise `at(statement(0).entry, owner->len) < ...` at statement 6
  produced `at(statement(6).entry, owner->len) < ...` — a different
  statement, after the `len` store. Under load terms the lowering mismatch
  masked this; under the invariant it surfaced as `push.contract`'s
  generated `apply` lowering its argument to `len + 1`. Re-reading at the
  new point is right for fact transport across a statement (the transport
  proved the cells unchanged) and wrong for recording where a premise was
  read, so the annotation now has two forms: `surface_with_source_site`
  re-reads, and `surface_anchored_where_unanchored` leaves operands that
  already name their point (`old` or `at`) untouched; premise recording
  uses the latter. (An earlier
  reading of this failure blamed a "pristine placeholder" memory; that
  was wrong — the empty base memory in `memory_with_symbolic_loadable_cells`
  is simply the function-entry snapshot's base, and
  `concretize_pristine_loads` rewrites entry-state loads to a later point.
  Whether that rewrite is still needed under the invariant is a separate
  question.)
- **Surface synthesis prefers anchored forms for load-variable facts.**
  A fact mentioning a load variable is anchored to the snapshot its cell
  was read from, so its program-point-anchored surface form stays correct
  at every later replay point, while a plain form is correct only until
  the cell changes. Both synthesis entry points (`checked_surface_fact_at_point`
  for conclusions, `checked_surface_comparison_fact_at_point` for
  premises) now try anchored forms first when canonicalizing at creation
  (switch-gated until the flip). With this and the annotation fix, the
  increment certificate in `push.contract` replays end to end.
- **Materialization cells hold load variables.** Done: the two
  consumers that recognized a materialization cell by its load-term shape
  (`canonical_memory_for_pointer_load`'s common-source jump and the
  outcome equality's unchanged-load check) take the source snapshot from
  the registry when the cell holds a load variable. `plan_explicit_nonstrict_transitive`
  supplies the two-step `<=` chain certificate. Three fixtures cleared;
  17 remain under the switch.
- **`rewrite` looks through load variables.** Done. With load terms,
  simp and `rewrite` substituted inside a load's address structurally
  (`load(m, data + v_old)` to `load(m, data + 0)` from `v_old == 0`). A
  load variable is opaque to that, so `rewrite_through_load_variable`
  rewrites the address of the load the variable stands for (registry
  view) and takes the canonical form of the rewritten load — equality
  substitution is congruent through a load whether it is written as a
  term or named by its variable, and no new certificate vocabulary is
  needed. All three rewrite walkers use it. Two fixtures cleared; 15
  remain under the switch.
- **Load-variable congruence (done).** `box_pipeline`'s `result == value`
  was not a cross-epoch problem: the callee's ensures named the written
  cell by `data + scaled(index)` and the later read by `data + 0`, and the
  link `index == 0` was sealed inside the first name. Names stay
  context-free (one name per epoch and address); the equality-graph walk
  (`bitvector_terms_equal_from_facts`) now follows a congruence edge from
  a load variable to the load variable for its address lowered through
  the ground equalities in scope (`load_variable_congruence_neighbor`,
  walked from both ends because the edge only points toward the lowered
  address). Regression:
  `load_variables_are_congruent_through_ground_index_equalities`. 14
  fixtures remain under the switch.
- **Names capturing bound variables (done).** Lowering a universal's
  body names `p[k]` with the bound `k` sealed inside the load variable's
  address, so instantiation by substitution could not reach it and the
  instance named a cell no read ever names. Substitution
  (`substitute_bitvector_variable`) now reaches through a load variable
  whose registered load mentions the substituted variable and takes the
  canonical form of the result; the universal trigger matcher
  (`guided_forall_condition_candidates`) views load variables as the loads
  they name. Names stay context-free. Regression:
  `substitution_reaches_through_a_load_variable_naming_a_bound_index`.
  11 fixtures remain under the switch, six of them expected-text.
- **Names in assumption-dependent reasoning (done).** Three kernel
  entry points keyed on the `MemoryLoad` shape and so ignored a name:
  `resolve_memory_load_term` (cell resolution under this context's
  facts), `memory_loads_proven_equal` (address equality decided by
  bounds, `p[j]` is `p[2]` under `j <= 2`, `not (j < 2)`), and
  `collect_bitvector_variables` (a bound index sealed in a name is free
  in the term, which the upper-bound case split keys on). Each now views
  a load variable as the load it names. With these the `bound_universal`
  fixtures prove in the kernel; what remains for them is surface
  synthesis of the proof object (below). Regression:
  `load_variables_compare_as_loads_under_bounds_pinned_indices`.
- **Mixed per-path `simp` captures (done).** Under names a leaf
  `assumption` can succeed on one execution path (`sort3`'s
  `sorted_range` after `unfold`) where the same claim on sibling paths
  falls to the implicit exact closer; the per-path captures then
  disagree and cannot be stitched without the forbidden branch skeleton.
  The drain now records whether the implicit closer would discharge each
  path, and when captures disagree while every path is so closable the
  tactic expands by removal — the certificate one path found is not
  evidence the others needed one. No default-mode fixture exercises the
  mixed case yet; `selected_pure_case_split_simp_expands_by_removal`
  covers it once the switch flips.
- **Expectation-text fixtures now include** the byte-predicate
  `instantiate(` (the claim closes in exact certification directly, so
  `simp()` legitimately expands to nothing), the linked-list retained
  `have observed == node->value` (the fact rides the step's `using`; the
  expansion replays under both modes), and the separation expansion's
  anchored `rewrite(at(statement(2).entry, left->len) == …)` forms.
- **Universals through names (done).** Two more places keyed on term
  shape: the quantified replay index (`alpha_bitvector_key`) keyed a load
  variable by its id, so a universal lowered to names and the recorded
  fact with a different binder id never shared a bucket and `instantiate`
  reported the fact "not exactly available"; and the free-variable
  collector did not reach a name's snapshot cells, so the finite context
  split (`j` pinned to `[0, 0]` by a cell written at `p[j]`) never
  fired. A name now keys as the load it names and collects the variables
  of its snapshot and address. Both `bound_universal` fixtures pass under
  the switch. Regressions:
  `quantified_replay_key_sees_through_load_variables`,
  `load_variable_free_variables_include_its_snapshot_cells`.
- **Diagnostics print names as loads (done).** `describe_bitvector`
  prints a load variable as `load(p[1])`, never its id; the negative
  diagnostic manifest passes under the switch. `step() using` now names
  the premise it could not find.
- **Remaining under the switch (5 expectation-text fixtures).** Three
  kernel expression tests asserting a raw load value (wrap the expected
  load in `canonical_term`); `expanded_branch_certificate…` (the branch
  condition anchors at `statement(1).entry`, the point that branched) and
  `source_expander_derives_separation…` (anchored `rewrite(at(...))`
  forms); the linked-list retained step in `resource_example_pipelines`
  (`rewrite(at(statement(5).entry, observed) == …)` replaces the `have`).
  These assertion edits were prepared and verified and are applied at
  the flip.
- **Step rule (decided 2026-08-21).** A step carries exactly the facts it
  is told to, one bounded frame check each against the statement's
  declared effect, with ownership by direct lookup; an uncarried fact
  stays at its pre-step snapshot and needs an explicit `transport`;
  comparison never does frame reasoning. Documented in
  `docs/concepts/proof-state-and-replay.md` ("What a step carries") and
  `docs/internals/verification-efficiency.md`. Consequences for the
  blockers below: the framed-epoch congruence edge is ruled out as a
  comparison move (it may serve as the checker behind a `transport`),
  and the repair for all three is the step's direct frame check seeing
  a composite resource's memory footprint.
- **Flip blockers (stage 4): three examples relied on structural snapshot matching.**
  Attempting the flip (2026-08-21) found proofs in `examples/` that only
  passed because the load-term world identified loads across snapshots
  without proof: `normalize_direct_atomic_memory_loads` and
  `canonical_c_memory_for_pointer_load` restrict a snapshot to the
  loaded block and so drop call-havoc markers (the known
  havoc-marker issue), and `old(x)` over the empty function-entry
  memory matched "the current value" through `concretize_pristine_loads`.
  Names are epoch-keyed and never match across an effect structurally, so these proofs fail under
  the switch and must be repaired — each needs a real frame proof, not
  a weaker example:
  - `input-cursor` (`input_cursor_shared_pipeline`): two `step() using`
    premises `old(left->len) == at(statement(N).entry, length)` claim the
    pre-`init` value of `left->len`, which nothing establishes; the old
    mode accepted them as the current value. Delete both premises. The
    later `transport(at(statement(5).entry, right->pos) == 0,
    right->pos == 0)` crosses `take(left)`'s havoc and needs `left` and
    `right` disjoint, which only the resource compositions know (two
    owned objects). Landed toward this: the DAG havoc hop and the direct
    effect-summary check consult the expanded compositions
    (`ranges_proven_disjoint_from_pointer_for_frame`), and a function's
    `local:` blocks are distinct from `ExternalArgument` memory
    (`blocks_proven_distinct`). With those the transport succeeds; the
    final `result == data[0]` then needs the names of `right->data` and
    `right->pos` on either side of `take` related — a **framed-epoch
    congruence edge** in the equality walk (name at the earliest epoch
    the facts frame the cell to, via `memory_dag_cell_source` under the
    context's facts, memoized by `memo_fingerprint`, run as a second
    pass only when recorded and congruence edges do not meet). That
    edge makes the example verify in 2.3 s (baseline 2.5 s) but lets
    smart search select derivations whose name-to-name transport the
    certificate vocabulary cannot write yet
    (`execute_until_expands_vector_storage_call_postconditions`,
    "fact transport has no recorded or synthesized Click comparison
    form"), so it waits for surface synthesis of name-form transports.
  - `owned-segmented-buffer` (done, under the step rule): the step's
    direct frame check now sees a composite's footprint. A single owned
    composite emits a `CResourceComposition` fact; the frame check expands
    it over the snapshot the fact holds at (memoized per composition and
    snapshot), so its members carry the live load variables; and range
    containment for the frame variant decides the endpoints from indexed
    bounds (`[0..1]` inside `[0..first_len]` under `1 <= first_len`). Two
    quadratic paths found on the way: the name-transport arm scanned the
    facts for a defining equation (now the registry origin), and
    `signed_constant_after_equality_normalization` tried every equality
    fact as a deep candidate for a load variable (now gated by address,
    as for a load term). 1.5 s under the switch against 1.3 s default.
  - `owned-vector` (`vector_grow`, else branch): lowering `have forall
    (k) … owner->data[k] == old(owner->data[k])` fails with
    `loadable(heap@k*4, 4)` unproved; the old mode proved it from the
    heap range loadability facts, which are present across the steps in
    both modes but absent from this `have`'s context under names (53
    facts versus 136) — the context selection for the `have` has not
    been traced yet. Indexing names under their address in the
    memory-load condition index and matching them in
    `condition_contains_contract_load` did not help and broke
    `execute_until_expands_vector_storage_call_postconditions`; not
    landed.
  Repro: flip `canonicalize_at_creation_enabled` to `true`, run
  `click verify` on the three sidecars. Acceptance: all examples verify
  under the flip with no weakened claims, the six assertion edits land,
  and the switch is deleted.
- **Cross-epoch load resolution.** Subsumed by the framed-epoch
  congruence edge above.
- **Chained bounds.** `owned_string_pop`'s expanded replay needs a
  two-fact bound chain that the single-fact `canonical_bound_holds` cannot
  answer, so it falls into `has_order_path_for_memory_resolution`, which is
  unmemoized inside fuel scopes and costs ~19k units per query. Either
  index two-hop bounds by canonical form or give the order search
  scope-safe memoization.
- **Loop invariant bundle preservation replay** (`bubble_pass3_max_suffix`,
  `bubble_sort3_two_pass_sorted`, `bound_universal_*`): "could not replay
  invariant closer" — the invariant-lowering paths compare or synthesize
  terms by load shape.
- **Smart `simp` goals left unproved** (`byte_slice_*`, predicate
  unfolding, quantified cells): planners that select facts or instantiate
  predicates by load shape.
- **Expected-text tests**: kernel expression tests asserting raw load
  values from symbolic loads, and expansion tests asserting certificate
  text (`at(function.entry, p[1])`, `bytes_contains(p, 0, n, 120u8)`).
  These update when the default flips; they are expectations of the old
  creation form, not consumer bugs.
- **Remaining typed evidence kinds.** Each `AtomicPropositionDerivationEvidence`
  constructor and replay checker that ties a premise to a goal by exact
  term gets the canonical tie already given to
  `Int32IncrementStrictlyIncreases`, as failures surface them.

### Stage 4: flip the default and simplify

With the suite green under the switch: make creation-time canonicalization
the default, delete the switch, and then remove the bridging that existed
only because terms were not canonical — load-variable resolution in
comparison positions, dual-term candidate lists, and the context-dependent
`assumption` availability relations. Land the deferred regressions below in
the same change.

## Constraints learned

- **Partial creation-time canonicalization splits terms.** Introducing
  load variables at one pointer-birth site while other creation paths still
  emitted load terms broke mutable-footprint containment in four fixtures
  and exact `assumption` selection in one (measured 2026-08-20). Comparison
  canonicalization removed most of that hazard; the invariant removes the
  rest by construction.
- **Recording a second, canonical copy of each fact is also a
  half-measure.** Asserting each load-mentioning fact's canonical form
  alongside the original at `assume_condition` time, while lowering still
  produced non-canonical terms, broke eight expansion fixtures with the
  switch off: citations lowered to non-canonical facts that no longer
  matched what replay contexts held. Stage 2 replaces rather than
  duplicates, and includes lowering, so citations and contexts agree.
- **Budget burns under the switch were search, not canonicalization.**
  Attribution spans on the explicit-range distinctness arms showed the
  ~917k-unit burn in `bitvector_index_in_range_shallow`'s searching bound
  arms; interning and canonicalization recorded no units. The indexed
  `canonical_bound_holds` fast path fixed the single-fact cases.
- **Certificate evidence follows the implicit-join design.** Canonical
  equality is definitional, so typed evidence cites its premise as the
  exact fact while the tie to a differently written goal base is a
  canonical comparison — deterministic, so it replays.

## Intended regressions

### Creation-time invariant

The stage-1 check, promoted to a test: run the fixture corpora with the
invariant check enabled and assert no violation. This is the regression
that keeps the invariant an invariant.

### Production representation

Evaluate loaded pointer and index expressions through the real symbolic
execution entry points. Recursively walk every resulting `PointerOffsetTerm`
and reject any reachable `Int32Scaled.value` containing a memory load.
Include a loaded array index and a pointer loaded from an opaque cell, and
assert that each load variable has its defining fact in the emitted facts.
The loaded-pointer half exists; the loaded-index half lands with stage 4.

### Coherence

Construct the same proposition through two creation paths: one from a load
whose pointer contains an old-snapshot loaded index, and one from a load
variable plus an explicitly equal index variable. Both must produce the
same canonical fact or a bounded simple certificate relating them.
Negative variants that omit the defining fact or change the cell between
snapshots must fail.

### Simple proof surface

Prove the `owned_string_push` null-terminator fact with explicit simple
steps: select the store effect, use the assignment and later field
equalities, and transport it to `owner->data[owner->len] == 0`, with no
smart tactic holding a premise the certificate cannot name.

### Deterministic scaling

Build the field-derived metadata-write transport at three input sizes,
measure deterministic verifier work units for the selected `have`, and
enforce a linear-up-to-indexing envelope. Keep
`mdtests/field_derived_precise_effect_after_metadata_write.md` as a corpus
canary within its ordinary budget; wall-clock time is diagnostic only.

## Acceptance criteria

- Every term in the proof state is canonical at creation, checked by the
  creation-time invariant regression, with defining facts as the only
  exemption.
- `canonical_term` is the one canonicalization function; comparison-time
  canonicalization remains only as a safety net, and no consumer depends on
  bridging between canonical and non-canonical terms.
- Load resolution closes name-to-name equality through proved facts
  across calls.
- Every atomic execution fact needed by a proof is selectable through a
  bounded simple certificate; the `owned_string_push` reproduction passes
  without broadening `assumption()`.
- Production-generated pointer offsets satisfy the structural regression
  for both loaded pointers and loaded indices.
- The deterministic scaling curve satisfies its envelope and the
  metadata-write corpus canary stays within budget.
- No C source, proof intent, tactic budget, verifier limit, or test
  strength is changed to route around a failure.
- `scripts/check.sh` is green, and this file plus its Open-list line are
  deleted when the invariant, its regressions, and the documentation land.
