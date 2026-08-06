# Keep one composite-resource unfold cheap

## Problem

While adapting the owned-vector proof to call the general `vector_push`, one
`unfold` of a four-part composite resource took several seconds. The resource
contained three struct fields and one capacity-sized backing range. The proof
also held facts from several earlier call snapshots.

An `unfold` is a simple tactic. Its cost should be determined primarily by the
resource body being projected, not by repeatedly renormalizing every unrelated
resource and snapshot fact in the ambient proof state. Changing the resource
layout or the example to avoid this state is not an acceptable repair.

## Intended regression

Add a focused mdtest with:

- a struct containing two scalar fields and a pointer field;
- a composite resource owning those fields and a symbolic backing range;
- declared loadability and separation facts;
- several unrelated recorded program points or opaque-call facts; and
- one explicit `unfold` of the composite resource.

The `unfold` must remain below the default simple-tactic budget. The test must
also compare its resulting resource context with the ordinary full
composition and normalization result. Add negative cases for overlapping
owned children and duplicate ownership.

At the kernel level, test incremental composition against full normalization
for different insertion orders, owned and viewed ranges, adjacent ranges,
contained ranges, symbolic endpoints, and assumptions added after the
original context was normalized.

## Design constraints

- Consume an exactly held folded composite without normalizing unrelated
  survivors merely as a side effect.
- Batch projection is acceptable only if it is observationally equivalent to
  ordinary checked composition.
- Do not assume that a context normalized under one assumption set remains
  normalized after resource-body facts strengthen those assumptions.
- Resource-body facts must not make overlapping owned children appear valid
  through circular reasoning.
- Prefer structural range operations before general entailment, but preserve
  a deterministic canonical form and test assumption-sensitive endpoints.
- Do not add an example-specific resource shape, increase tactic budgets, or
  retain a slow successful run.

## Acceptance criteria

- The focused `unfold` passes the default simple-tactic budget with comfortable
  headroom.
- Incremental and full composition agree on validity, ownership, consumption,
  and observable facts across the regression matrix.
- Invalid overlapping or duplicate ownership is still rejected.
- Diagnostics remain concise when unfolding is invalid.
- Profile, expansion, audit, mdtests, examples, and the default test suite
  pass without changing C or weakening the resource definition.
