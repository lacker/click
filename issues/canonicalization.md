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
  behind `CLICK_OFFSET_INDEX_LOAD_VARIABLES=1`, off by default; three
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

### Stage 2: canonicalize at every creation point, behind one switch

Rename the switch to `CLICK_CANONICALIZE_AT_CREATION=1` and make it govern:

- **Symbolic execution.** Facts pass through canonicalization where
  `ExecutionPureFact` values are built (`public`, `certified`, condition
  facts), with two exemptions: defining facts, and certified store records,
  whose structured `CertifiedMemoryStore` data stays as recorded while the
  proposition is canonical. Values in offsets use
  `canonicalized_offset_index_term` (already implemented).
- **Lowering.** The kernel proposition produced for a Surface Click
  proposition is canonicalized before it is recorded, compared, or cited, so
  a certificate citation `owner->len < owner->cap` lowers to the canonical
  fact and a replay context rebuilt from citations holds canonical facts.
- **Contract and spec evaluation.** Range endpoints, composite arguments,
  segment endpoints, and loadability propositions canonicalize at
  construction (`evaluate_spec_resource_at_state`,
  `lower_spec_memory_loadable_at_state`, `evaluate_effect_segment`,
  `evaluate_loop_effect_segment`).
- **Resource fact projection.** The facts projected from composite
  resource declarations and resource contexts canonicalize where they are
  produced (`project_resource_context_observable_facts`,
  `append_composite_resource_declared_facts`,
  `evaluate_composite_resource_fact_propositions`,
  `LegacyResourcePureFacts::new`).

Comparison-time canonicalization stays on throughout as the safety net.

### Stage 3: fix the consumers the switch exposes

Run the suite under the switch and repair each consumer that still assumes
a load term. Two are already characterized:

- **Cross-epoch load resolution (required feature, not a gap).** Across a
  call whose footprint may write a cell, the read before and the read after
  receive different load variables (the DAG walk cannot cross the call
  havoc). Their equality is a proved fact from the callee's ensures.
  Load resolution (`bitvector_terms_equal_for_memory_resolution`'s
  load-variable arm and the store-cell lookup in
  `evaluate_c_memory_load_paths`) must consult the equality graph's
  name-to-name edges. Reproductions: `box_pipeline`'s `result == value`
  (`modular_call_snapshot_anchor_replays_with_owned_resource`) and
  `input_cursor_shared_pipeline`'s Ensure(4).
- **Chained bounds.** `owned_string_pop`'s expanded replay needs a
  two-fact bound chain that the single-fact `canonical_bound_holds` cannot
  answer, so it falls into `has_order_path_for_memory_resolution`, which is
  unmemoized inside fuel scopes and costs ~19k units per query. First
  confirm the exact missing bound with the attribution spans already in
  place; then either index two-hop bounds by canonical form or give the
  order search scope-safe memoization.
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
