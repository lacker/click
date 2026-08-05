# Isolate verifier state between parallel tests

## Problem

A normal parallel `cargo test` run made
`loop_phase_proofs_can_unfold_invariant_predicates` fail with exact symbolic
execution producing no valid paths. The same test passed immediately when run
alone. Proof results must not depend on which unrelated test happens to run at
the same time.

Likely shared-state candidates include fresh-identity allocation, deadline or
budget accounting, memoization, and certificate-capture state. Thread-local
state is acceptable only when every verification run initializes and tears it
down deterministically.

## Intended design

- Each top-level verification owns its mutable search, budget, deadline,
  memoization, and certificate-capture state.
- Process-wide state may allocate globally unique identities, but interleaving
  allocations cannot change proof meaning or success.
- A test's class budget measures its own verifier work rather than wall-clock
  time lost to unrelated tests.

## Regression

Run the loop-phase proof together with several verifier-heavy tests on multiple
test threads, repeatedly. Its result and emitted certificate must equal a
serial run. Add a lower-level concurrency regression for whichever shared state
caused the failure.

## Acceptance criteria

- Repeated parallel and serial runs have the same proof outcome.
- No global reset can corrupt another in-flight verification.
- The default parallel `cargo test` suite is reliable and green.

