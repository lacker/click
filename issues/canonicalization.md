# Canonicalization needs a proof-grounded model

## Violated invariant

Click needs one logically grounded model for canonical proof terms. For every
supported term, that model must say:

- which differing terms are equal by definition;
- which changes require an explicit proved equality;
- which evidence authorizes selecting a representative;
- how the representative and its evidence are recorded; and
- how a simple proof can select and consume every fact the verifier emits.

Canonicalization must be deterministic and idempotent over that model. Its
result must not depend on whether a term came from C execution, Surface Click
lowering, a premise, a goal, a resource-range endpoint, or a nested pointer
offset. Consumers such as `assumption()` must not guess which normalization
path ran, compose competing equivalence relations, or expand a load
variable back into retained memory snapshots.

Every atomic fact emitted by C execution must also be selectable and
consumable by bounded simple proof steps. Smart tactics may compose those
steps, but must not possess reasoning authority or internal vocabulary that
an explicit replayable certificate cannot express. Scalable verification is
part of the same invariant: canonicalization and fact selection must remain
linear up to the repository's documented indexing allowances as unrelated
snapshots and facts are added.

## Current model gap

Click currently has overlapping mechanisms without one shared contract:

- `canonicalize_atomic_loads` resolves cached cells and normalizes
  snapshot-dependent load terms using symbolic-memory provenance;
- `PureFactContext::canonical_bitvector` selects representatives using
  explicit equalities in the proof context; and
- load variables give selected loads one stable kernel variable.

Memory provenance and explicit equality are different sources of proof
authority. That distinction must remain explicit, but it does not justify
competing output forms or producer- and consumer-specific combinations of
the mechanisms. The load-variable registry may identify a proposed
representative; registry membership alone is never proof that two terms are
equal. Every load variable must carry an exact defining fact.

The incomplete model appears in three related ways.

### Production pointer offsets

Production evaluation must not place a raw `Bitvector32Term::MemoryLoad`
inside pointer-offset arithmetic. Loaded pointers and indices must first be
given the model's stable representation, with the defining evidence emitted
beside it. The implementation does this in
`canonicalized_pointer_value_from_int_cell` and
`canonicalized_symbolic_load_value`, and a structural regression now walks
the loaded-pointer case from the real evaluation entry points
(`src/kernel/tests/canonicalization_tests.rs`). Loaded **indices** remain
unenforced: kernel pointer addition (`apply_c_add`), spec pointer-offset
evaluation (`evaluate_spec_pointer_offset_paths`), the lang-side
effect-segment evaluator (`evaluate_effect_segment` in
`src/lang/click/checking/effects.rs`), and resource-range endpoint
evaluation all still admit raw loads. Kernel tests that deliberately
construct raw load-bearing offsets do not establish the production
invariant.

**Producer adoption is atomic.** Introducing load variables at one
offset-birth site while other producers of the same fact family still
emit load terms splits one load identity into two terms that only a
proved equality could reconnect, which frame checks and exact `assumption`
matching rightly refuse to assume. Measured on 2026-08-20 by
canonicalizing only `apply_c_add` and the spec offset path: mutable-
footprint containment failed in four contract fixtures (write pointers
using load variables, footprint segments using load terms, e.g. `vector_push.contract` "write to
`owner[((v… + v…) - v…)]` is outside the mutable footprint" with segments
written `load(arg-memory@v… * 4)`), an expanded pipeline's exact
`assumption` selection lost a fact to mixed terms
(`input_cursor_shared_pipeline.contract`), and a frame tactic blew its
100ms budget (`owned_string_pop.contract`).

**Comparison-side canonical keying landed 2026-08-20** and removes most of
the mixed-term hazard: the equality graph, affine cancellation, and
the exact frame matchers key by canonical form, and surface synthesis
resolves load variables through the registry. A second round extended the
canonical joins into the arithmetic provers: the memory-resolution
equality's deep arm compares full canonical forms (load variables included), the
signed-order-bounds index is dual-keyed under the fact's endpoint term and its
canonical form, and the increment/decrement overflow helpers match their
base by canonical form. With those, mutable-footprint containment proves
with load variables for indices.

Certificate provenance for canonically-decided arithmetic now follows the
implicit-join design: canonical-form equality is definitional, so typed
evidence cites its premise as the exact fact while the tie between the
premise and the goal's differently written base is a
canonical comparison, which is deterministic and replays. The
signed-order-bounds index carries each fact's own endpoint term so
evidence reached through the canonical alias still cites the exact fact
(`signed_order_bound_entries`), and `Int32IncrementStrictlyIncreases`
construction and replay tie canonically. Remaining typed evidence kinds
get the same treatment as failures under the switch surface them.

Load variables for indices stay behind `CLICK_OFFSET_INDEX_LOAD_VARIABLES=1` with two
remaining fronts, measured 2026-08-21:

- **Chained-bound order search cost.** The fold-family budget burn is
  fixed: attribution spans on the explicit-range arms showed the units
  in `bitvector_index_in_range_shallow`'s searching bound arms (not in
  interning or canonicalization), and the canonical-keyed
  `canonical_bound_holds` fast path — an indexed single-fact bound
  lookup joining endpoints by canonical form — answers those queries
  before any search runs (`push.contract` passes under the switch). What
  remains is the same shape one step deeper: `owned_string_pop`'s
  expanded replay burns ~760k units in `range membership: index in
  range` on bounds needing a two-fact chain (`len-1 < len <= cap`),
  which the single-fact lookup cannot answer, so the unmemoized
  `has_order_path_for_memory_resolution` search runs per candidate per
  query (`resolution_query_memo_id` is `None` inside fuel scopes).
  Either the chained lookup becomes canonical-keyed and indexed, or the
  order search gains scope-safe memoization.
- **Cross-call value tracking.** `box_pipeline`'s `result == value` and
  `input_cursor_shared_pipeline`'s Ensure(4): a caller's read after a
  callee's store does not resolve against the store when the indices receive
  different load variables at different derivation epochs.

A fact-recording companion (also asserting each load-mentioning fact's
canonical form at `assume_condition` time) was tried and rejected: it
changes fact-set content globally and broke eight expansion fixtures with
the switch off.

### Canonical facts without a simple certificate

The proof-object migration exposes a concrete mismatch in
`owned_string_push`. After storing the null terminator, the proof needs the
already-known fact

```text
owner->data[owner->len] == 0
```

The stored fact uses the execution engine's canonical index, while a Surface
Click term retains an equal load of the old `owner->len`; the outer data
load may also use another snapshot. The context contains the assignment
equality and memory-provenance evidence needed for the conversion.

Bounded smart reasoning derives the goal after receiving the explicit
assignment equality, but certificate lowering reports that the canonical
store fact has no replayable Surface Click form at that proof point.
Historical `at(statement(...), ...)` forms lower back to the raw load
rather than naming the recorded store fact. Consequently `transport`,
`rewrite`, `normalize`, and `assumption` cannot express the short derivation
as simple steps even though the kernel can find it.

Do not solve this by adding equality or arithmetic search to `assumption()`,
expanding load variables back into snapshots, treating the registry as
proof authority, or improving smart search without first making the
derivation explicitly replayable.

### Unpinned scaling

Canonical loaded offsets fixed the recursive load-in-offset failure behind
`field_derived_precise_effect_after_metadata_write`, and that proof is green.
Its single-corpus timing does not establish the required complexity bound.
Adding unrelated snapshots or facts must not restore superlinear work in its
explicit transport path.

## Intended regressions

### Production representation

Evaluate representative loaded pointer and index expressions through the
production APIs. Recursively walk every resulting `PointerOffsetTerm` and
reject any reachable `Int32Scaled.value` containing a `MemoryLoad`. Include a
loaded array index and a pointer loaded from an opaque cell. Assert that each
load variable has its exact defining equality in the emitted facts.

### Coherence and authority

Construct the same proposition through two production paths: one from a load
whose pointer contains an old-snapshot loaded index, and one from a canonical
load name plus an explicitly equal index variable. With the exact definition
and unchanged-cell provenance, both paths must produce the same canonical
fact or a bounded simple certificate relating them. Negative variants that
omit the defining equality or change the cell between snapshots must fail.

### Simple proof surface

Prove the `owned_string_push` null-terminator fact with explicit simple steps:
select the store effect, use the assignment and later field equalities, and
transport it to `owner->data[owner->len] == 0`. The proof must not depend on a
smart tactic possessing an internal premise that certificate replay cannot
name.

### Deterministic scaling

Build the field-derived metadata-write transport at least three input
sizes, measure deterministic verifier work units for the selected `have`,
and enforce a linear-up-to-indexing envelope. Keep
`mdtests/field_derived_precise_effect_after_metadata_write.md` as a corpus
canary below the ordinary tactic budget; wall-clock time is diagnostic only.

## Acceptance criteria

- The canonicalization model documents its equivalence relations, proof
  authorities, representative-selection rule, and fixed composition order.
- Canonicalization is deterministic and idempotent for every supported term
  form exercised by premises, goals, memory ranges, and pointer offsets.
- C execution and Surface Click proof producers use that model rather than
  creating consumer-specific normal forms.
- Every load variable has an exact defining fact, and registry
  membership alone never proves equality.
- Every atomic execution fact needed by a proof is selectable through a
  bounded simple certificate; the owned-string reproduction passes without
  broadening `assumption()` or relying on unreplayable smart reasoning.
- Production-generated pointer offsets satisfy the no-raw-load structural
  regression.
- The deterministic scaling curve satisfies its stated envelope and the
  metadata-write corpus canary remains within its ordinary budget.
- No C source, proof intent, tactic budget, verifier limit, or test strength
  is changed to route around a failure.
- `scripts/check.sh` is green, and this file plus its Open-list line are
  deleted when the model, implementation, regressions, and documentation
  land.
