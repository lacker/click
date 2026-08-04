# Open issues

`master` is expected to pass the default test suite. Known-broken or
pathologically slow cases belong in explicit quarantine lists in
`tests/mdtests.rs` and `tests/examples.rs`, with a corresponding issue here.

## Partial correctness and recursion

Click's existing loop invariants are naturally partial-correctness proofs, but
function certification and kernel execution propositions currently assume a
complete return frontier. Resolve that mismatch before adding recursive C
calls:

1. [Separate partial-correctness summaries from concrete execution](partial-correctness-kernel-boundary.md).
2. [Certify C functions that may or must diverge](diverging-c-function-certification.md).
3. [Verify recursive C functions by contract](recursive-c-function-contracts.md).
4. [Add well-founded recursion to pure Click functions](well-founded-pure-click-recursion.md).
5. [Add optional C termination certificates](optional-c-termination-certificates.md)
   only after partial C recursion is sound.
6. [Add a perpetual-service example](perpetual-service-example.md) once the
   first two issues land.

The first two issues are correctness cleanup, not optional recursion features.
The third and fourth deliberately use different proof models: C contracts are
partial by default, while a pure Click function must produce a value. Optional
C termination is useful but must not block ordinary recursive verification.

A true input-stream example remains a later design problem. Click can presently
prove safety invariants for an indefinitely running loop, but it has no event
trace, external-input, fairness, or productivity semantics with which to state
the interesting stream-processing guarantee. The perpetual-service example is
intentionally smaller and honest about that boundary.

## Independent cleanup

- [Compose pure facts through opaque-call local results](opaque-call-local-result-fact-composition.md).

Keep one file per independent open problem. Put durable implementation design
in `docs/`, and delete an issue when its fix, regression coverage, and
documentation land.
