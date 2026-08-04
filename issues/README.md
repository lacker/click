# Open issues

`master` is expected to pass the default test suite. Known-broken or
pathologically slow cases belong in explicit quarantine lists in
`tests/mdtests.rs` and `tests/examples.rs`, with a corresponding issue here.

## Partial correctness and recursion

Click's C contracts now use partial correctness consistently: concrete
execution is separate from modular verification, and safe functions need not
have a return frontier. The remaining recursion work is:

1. [Add optional C termination certificates](optional-c-termination-certificates.md)
   only after partial C recursion is sound.
2. [Add a perpetual-service example](perpetual-service-example.md).

Recursive C contracts are partial by default, while recursive pure Click
functions now require a checked `decreases` measure because they must produce a
value. Optional C termination is useful but must not block ordinary recursive
verification.

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
