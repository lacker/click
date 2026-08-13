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

## 2026-08-13 progress: certificate and spelling insertion indexes

`SimpleProofBuilder` no longer accumulates replay-visible certificate facts in
a bare vector. `ProofFactStore` keeps insertion order for emitted certificates
and diagnostics while maintaining an exact ordered index; adding a fact no
longer scans every prior certificate fact. All mutation sites now use the
store, including statement execution, planned transports, and replay-builder
construction. A focused invariant regression covers insertion, duplicate
suppression, order, and indexed retention, while the existing explicit-step,
transport, exact-assumption, and surface-spelling scaling curves remain green.

`SurfacePropositionMap` likewise separates deterministic presentation from
membership. Kernel-to-surface insertion uses a debug-key bucket followed by
collision-safe structural equality only inside that bucket, and each surface
spelling's kernel lowerings have an exact ordered index. Thus unrelated prior
spellings and lowerings are not rescanned on every record operation.

The issue remains open. `available_kernel` still receives an unindexed
`&[Proposition]`, so resolving one lowering can scan the caller's complete
available slice. Several proof contexts also retain ambient facts as vectors.
Closing the issue requires routing these callers through the persistent fact
store (or an exact `Assumptions` view) and giving proposition keys stable
shallow identities rather than relying on deep ordered comparisons.

Condition facts that contain memory-load spellings now have a derived index
keyed by the loaded pointer's snapshot-blind structural fingerprint. Contract
lowering checks that exact bucket first, then retains a same-block fallback so
proved pointer aliases with different syntax remain accepted. The full
snapshot/effect relation remains the authority for every candidate. A
four-size deterministic regression holds one load spelling fixed while adding
same-block loads at unrelated pointer shapes and requires constant query work.

Idempotently assuming an already-present condition also preserves all shared
fact/index storage instead of triggering `Arc::make_mut` copies of the complete
context. New condition insertion is still copy-on-write and therefore linear
in the accumulated context; a genuinely persistent fact store remains
necessary to meet the acceptance criterion for that case.

Loadability facts now carry the same pointer-shape index in addition to their
allocation-block index. The loadability prover tries the exact structural
shape bucket before same-block alias fallbacks, and every candidate still has
to pass the existing snapshot and range proof. A second four-size regression
holds one fixed loadability query while adding same-block ranges at unrelated
pointer shapes and requires constant candidate work. This bounds the common
field/range lookup; genuinely aliased spellings and range arithmetic can still
enter the broader proof path.
