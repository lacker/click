# Two sorts of canonicalization

## Violated invariant

A proof proposition should have one canonical representation when it enters
the proof context, regardless of which lowering or evaluation path produced
it. Consumers such as `assumption()` should not need to guess which
normalization path ran, compose several notions of representation equality,
or expand a proof-side name back into a snapshot-bearing term.

Every atomic fact emitted by C execution must also be selectable and
consumable by a bounded simple proof step. Smart tactics may compose those
steps, but must not possess reasoning authority or internal vocabulary that
an explicit replayable certificate cannot express.

Click currently has two overlapping forms of term canonicalization:

- memory canonicalization, principally through `canonicalize_atomic_loads`,
  resolves cached cells and normalizes snapshot-dependent memory-load
  spellings using symbolic-memory provenance; and
- equality-context canonicalization, principally through
  `PureFactContext::canonical_bitvector`, selects a preferred spelling using
  explicit equalities already present in the proof context.

Canonical load variables add a stable proof-side name for the first form and
must be accompanied by an exact defining equality. The two sources of proof
authority are legitimately different, but that does not justify competing
normal forms or producer- and consumer-specific combinations of them. Today
the result can depend on which helper ran, in which order, and whether the
term was a premise, goal, memory-range endpoint, or nested pointer offset.

## Current reproduction

The proof-object migration exposes this in `owned_string_push`. After the
null terminator is stored, the final proof needs the already-known fact

```text
owner->data[owner->len] == 0
```

One spelling reaches the context with an index like `index + 1`; another
retains the equal load of the old `owner->len`, and the outer data load may
refer to a different memory snapshot. The context contains both the exact
index equality and the memory-provenance facts needed to justify the match,
but the two propositions do not arrive at `assumption()` in one canonical
form.

Do not solve this by making `assumption()` into a general equality-and-memory
search, by expanding canonical names back into retained snapshots, or by
treating the canonical-name registry as proof authority.

An attempted proof-only workaround showed that `transport(...)` cannot yet
name this conversion. The kernel's bounded smart reasoning derives the goal
once given the assignment equality between `index` and the old `owner->len`,
but certificate lowering reports that the canonical store fact has no
replayable Surface Click spelling at this proof point. Historical
`at(statement(...), ...)` spellings lower back to the raw load rather than the
canonical index used by the recorded store. Thus a local transport remains a
desirable workaround, but it is not currently expressible without addressing
the producer-side canonicalization or certificate surface described here.
This architectural issue should still not block otherwise independent
migration slices.

## Intended regression

Construct one proposition through two production paths:

1. from a load whose pointer contains an old-snapshot loaded index; and
2. from the canonical load name and an explicitly equal index variable.

Provide the exact defining equality and the provenance that the referenced
cell is unchanged. Record both propositions through the public producer-side
proof API and assert that they enter the proof context in the same structural
form. Negative variants must omit the defining equality and change the cell
between snapshots; neither variant may canonicalize the propositions to the
same form.

## Acceptance criteria

- There is one documented producer-side canonicalization pipeline for terms
  and propositions, with a fixed order for memory-provenance normalization
  and explicit-equality representative selection.
- Premises, goals, memory-resource ranges, and nested pointer offsets use that
  pipeline rather than choosing their own combinations of normalizers.
- The two proof authorities remain explicit: provenance justifies memory
  representation changes, while recorded equalities justify equality-class
  changes.
- Every canonical load name used by the pipeline has an exact defining fact;
  registry membership alone never proves equality.
- `assumption()` does not gain arithmetic search, reverse name expansion, or
  a new consumer-only canonical form.
- The owned-string conversion is expressible with an explicit simple
  certificate; smart reasoning must not succeed with a derivation that its
  certificate lowering cannot replay.
- The positive and negative production-path regressions pass under a green
  `scripts/check.sh`, with no C changes or verifier-limit increases.
- This file and its Open-list line are deleted when the unified pipeline,
  regression coverage, and documentation land.
