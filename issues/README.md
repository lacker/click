# Open issues

`master` is expected to pass the default test suite. Known-broken or
pathologically slow cases belong in explicit quarantine lists in
`tests/mdtests.rs` and `tests/examples.rs`, with a corresponding issue here.

## Partial correctness and recursion

Click's C contracts now use partial correctness consistently: concrete
execution is separate from modular verification, and safe functions need not
have a return frontier. The `perpetual-service` example demonstrates that
boundary with an opaque step call and composite ownership.

Recursive C contracts are partial by default, while recursive pure Click
functions now require a checked `decreases` measure because they must produce a
value. Optional C termination now uses separate kernel-checked `decreases`
evidence and does not block ordinary recursive verification.

A true input-stream example remains a later design problem. Click can presently
prove safety invariants for an indefinitely running loop, but it has no event
trace, external-input, fairness, or productivity semantics with which to state
the interesting stream-processing guarantee. A true stream example is
intentionally deferred until those semantics exist.

## Recursive-function roadmap

The base recursion model and the `recursive-zero-list` integration example are
in place. The remaining work is to audit the composition boundary, then add the
two proof capabilities that the example deliberately cannot claim:

1. [Audit recursive resource/call composition](recursive-resource-call-composition-audit.md)
   against that example and fix only concrete, ordinary warts it reveals.
2. [Prove C termination by recursive-resource descent](structural-c-termination.md),
   without changing partial correctness or trusting pointer syntax as a rank.
3. [Add explicit induction for pure Click theorems](pure-function-induction.md),
   as a proof rule separate from C recursion and C termination.

The example and audit are intentionally smaller than the two language
features. Structural C termination depends on certified resource ancestry;
pure induction depends on a kernel-checked well-founded proof rule. Neither
should be smuggled into `simp`, opaque-call application, or ordinary recursive
contract certification.

Keep one file per independent open problem. Put durable implementation design
in `docs/`, and delete an issue when its fix, regression coverage, and
documentation land.
