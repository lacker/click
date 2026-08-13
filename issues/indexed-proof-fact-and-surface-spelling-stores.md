# Exact proof operations linearly scan fact and surface-spelling vectors

The kernel's `Assumptions` has ordered exact sets, but much of proof replay
still carries `Vec<Proposition>` and repeatedly uses linear `contains`,
deduplication, cloning, and reconstruction of assumptions. The reverse side of
`SurfacePropositionMap` is also a vector; resolving one surface premise first
scans spellings and then scans the available fact slice.

Consequently, `assumption`, explicit `step() using`, theorem application, and
fact transport can cost proportional to all ambient facts rather than the
premises they name. Accumulating facts across a long simple script permits
quadratic behavior.

## Required design

Introduce one persistent proof-fact store with stable proposition identities,
ordered presentation, exact membership, and theory-specific indexes. Surface
spellings need a true bidirectional map keyed by interned surface and kernel
proposition identities. Adding a fact should incrementally update an
`Assumptions` view instead of rebuilding it from a vector.

Ordering for deterministic diagnostics and certificate printing must be kept
separate from the membership index. Equivalent-but-not-exact reasoning must
remain an explicit theory operation; an exact lookup must not silently broaden
into search.

## Regression design

Verify a fixed exact `assumption`, `step() using`, and transport while adding
increasing numbers of unrelated facts and unrelated surface spellings. Each
operation should remain logarithmic after proposition parsing/interning. Add a
separate linear-output test that explicitly names increasing premise counts.

Scaling axis: `exact_assumption_scales_near_linearly_with_unrelated_ambient_facts`
now guards the fixed exact-assumption case while growing both ambient facts and
their recorded surface spellings. The default gate now also covers a fixed
explicit `step() using`, a fixed explicit transport, and many shallow surface
spellings that normalize to one kernel fact. These end-to-end curves protect
aggregate behavior; named-operation attribution is still required to prove
that the individual lookup itself does not hide a linear ambient scan beneath
unavoidable linear project setup.

## Acceptance criteria

- Exact fact and surface-spelling lookup is indexed in both directions.
- Adding one fact does not clone or rebuild the complete context.
- Unrelated facts do not materially change fixed-tactic deterministic work.
- Explicitly listing `K` premises costs `O(K polylog N)`.
- Diagnostics retain deterministic source order.
