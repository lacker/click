# Finish the `SimpleProof` planning boundary

Click now has the important smart/simple safety boundary: a successful smart
tactic constructs a typed `SimpleProof`, containing only surface-expressible
`SimpleProofStep` values, and independently replays it before success is
accepted. `CertifiedStatementReplay` and `CertifiedLoopSummaryReplay` no longer
exist.

The implementation below that boundary is still transitional. Smart search
usually produces an `InternalProofPlan` whose `Vec<ProofTactic>` mixes parsed
surface tactics with internal planning operations such as
`CertifiedStatementStep`, `CertifiedLoopSummaryStep`, and exact derivations.
Click then replays that plan while mutating `SimpleProofBuilder` to reconstruct
the typed proof. Verified theorem results also retain expanded
`Vec<ProofTactic>` values and convert them back into `SimpleProof` later.

This is safe enough to enforce expansion today, but it preserves the fragile
shape that made provenance omissions difficult to localize. Treat the cleanup
as an independent refactor after the correctness gates are green; do not mix it
with a new resource feature or change proof search heuristics to make the
refactor pass.

## Desired boundary

```text
smart planning
    -> construct SimpleProof directly from checked planning evidence
    -> independently replay SimpleProof
    -> print it by structural traversal
```

Kernel derivations and certified C transitions remain valid internal evidence.
They should live in a dedicated planning representation rather than variants
of the parsed `ProofTactic` AST, and they must be consumed explicitly while
constructing the corresponding `SimpleProofStep`.

## Independently green chunks

1. Give internal planning its own typed operations instead of storing
   replay-only variants in `Vec<ProofTactic>`.
2. Make planning operations construct or return their `SimpleProofStep`
   contribution explicitly, removing mutation of `SimpleProofBuilder` as a
   provenance-recording side channel.
3. Store completed expansions as `SimpleProof` in verified results; convert to
   `ProofTactic` only at the parser/printer boundary.
4. Give construction and replay errors stable paths into the structured
   `SimpleProof`, distinguishing planning failure, missing surface support,
   construction failure, and replay disagreement.
5. Remove obsolete internal tactic variants, conversions, classifications, and
   recorder state once all smart tactics use the typed path.

The pending `simp() using` migration remains separate: `derive` cannot be
removed from `SimpleProofStep` until the explicit arithmetic and transport
certificate vocabulary described in
`simp-using-expands-to-explicit-certificates.md` exists.

## Acceptance criteria

- Every successful smart tactic produces the same typed `SimpleProof` result
  without first encoding its plan as surface `ProofTactic` values.
- Internal statement, loop, derivation, transport, and frame evidence cannot
  appear in the parsed surface tactic enum.
- Constructing a `SimpleProof` does not depend on replay-time mutation of a
  parallel recorder.
- Verified expansion results retain `SimpleProof` directly.
- Printing is purely structural, and independent replay work is proportional
  to the explicit simple steps.
- Failures identify the boundary and stable proof path involved.
- `click profile`, `click expand`, and `click audit` consume the same completed
  proof and agree about expansion success.
