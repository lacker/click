# Canonicalization needs a proof-grounded model

## Violated invariant

Click needs one logically grounded model for canonical proof terms. For every
supported term, that model must say:

- which differently spelled terms are representation-identical;
- which changes require an explicit proved equality;
- which evidence authorizes selecting a representative;
- how the representative and its evidence are recorded; and
- how a simple proof can select and consume every fact the verifier emits.

Canonicalization must be deterministic and idempotent over that model. Its
result must not depend on whether a term came from C execution, Surface Click
lowering, a premise, a goal, a resource-range endpoint, or a nested pointer
offset. Consumers such as `assumption()` must not guess which normalization
path ran, compose competing equivalence relations, or expand a proof-side
name back into retained memory snapshots.

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
  snapshot-dependent load spellings using symbolic-memory provenance;
- `PureFactContext::canonical_bitvector` selects representatives using
  explicit equalities in the proof context; and
- canonical load variables give selected loads stable proof-side names.

Memory provenance and explicit equality are different sources of proof
authority. That distinction must remain explicit, but it does not justify
competing output forms or producer- and consumer-specific combinations of
the mechanisms. A canonical-name registry may identify a proposed
representative; registry membership alone is never proof that two terms are
equal. Every canonical load name must carry an exact defining fact.

The incomplete model appears in three related ways.

### Production pointer offsets

Production evaluation must not place a raw `Bitvector32Term::MemoryLoad`
inside pointer-offset arithmetic. Loaded pointers and indices must first be
given the model's stable representation, with the defining evidence emitted
beside it. The implementation does this in
`canonicalized_pointer_value_from_int_cell` and
`canonicalized_symbolic_load_value`, but no structural regression walks
pointers from the real evaluation and lowering entry points. Kernel tests
that deliberately construct raw load-bearing offsets do not establish the
production invariant.

### Canonical facts without a simple certificate

The proof-object migration exposes a concrete mismatch in
`owned_string_push`. After storing the null terminator, the proof needs the
already-known fact

```text
owner->data[owner->len] == 0
```

The stored fact uses the execution engine's canonical index, while a Surface
Click spelling retains an equal load of the old `owner->len`; the outer data
load may also use another snapshot. The context contains the assignment
equality and memory-provenance evidence needed for the conversion.

Bounded smart reasoning derives the goal after receiving the explicit
assignment equality, but certificate lowering reports that the canonical
store fact has no replayable Surface Click spelling at that proof point.
Historical `at(statement(...), ...)` spellings lower back to the raw load
rather than naming the recorded store fact. Consequently `transport`,
`rewrite`, `normalize`, and `assumption` cannot express the short derivation
as simple steps even though the kernel can find it.

Do not solve this by adding equality or arithmetic search to `assumption()`,
expanding canonical names back into snapshots, treating the name registry as
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
canonical name has its exact defining equality in the emitted facts.

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
- Every canonical load name has an exact defining fact, and registry
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
