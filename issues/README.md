# Open issues

`master` is expected to pass the default test suite. Known-broken or
pathologically slow cases belong in explicit quarantine lists in
`tests/mdtests.rs` and `tests/examples.rs`, with a corresponding issue here.

Do not normalize verifier or tooling failures as part of proof development.
When work exposes an engine problem, either fix it with a focused regression in
the current chunk or write an issue before continuing. These problems take
priority over new language features and over making an example pass. Restore a
green, check-in-ready checkpoint before resuming the paused feature. In
particular, always track:

- a tactic that crosses its class budget, even if a larger command eventually
  finishes;
- a search that reports success but whose emitted or internal certificate does
  not replay;
- `click profile`, `click expand`, and `click audit` disagreeing about the same
  proof site;
- diagnostics large enough to obscure the actionable cause;
- proof scripts that must preserve irrelevant spellings or route calls through
  artificial helpers to compensate for verifier behavior; and
- a kernel/resource-model error discovered while building an example.

The issue should contain a small intended regression, the violated invariant,
and acceptance criteria. Do not leave the only reproduction in an uncommitted
large example or quarantine a regression without its issue.

## Allocation and proof-tooling follow-up

Runtime-sized allocation/free and the independently verifiable general vector
push are implemented in focused example projects. Composing allocation, copy,
replacement, and free into vector growth exposed distinct remaining bugs:

1. [Replay assumption-derived premises selected by `execute`](smart-execute-derived-premise-replay.md).
2. [Compose runtime allocation into owned-vector growth](owned-vector-runtime-growth.md)
   after the blocking invariants above are restored.

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

The base recursion model, the `recursive-zero-list` integration example, its
composition audit, structural C termination, and explicit pure theorem
induction are in place. Their durable behavior is documented in the language,
kernel, proof-tactic, and pure-function guides. There are no open recursion
roadmap issues at present.

Keep one file per independent open problem. Put durable implementation design
in `docs/`, and delete an issue when its fix, regression coverage, and
documentation land.
