# Correctness tests depend on machine speed

## Problem

The default correctness suite can fail when otherwise-valid smart tactics hit
their two-second production deadline under concurrent or sustained load. The
same proof succeeds immediately when rerun alone. This makes `cargo test` red
because of the machine's current throughput rather than a semantic regression.

`CLOCK_THREAD_CPUTIME_ID` correctly excludes time while a verifier thread is
descheduled, but CPU duration is still not a deterministic work measure:
parallel tests, thermal state, and CPU frequency change how much prover work
fits into two CPU seconds. Serializing the mdtest harness avoids scheduler
contention but does not avoid throughput changes after the example suite.

Observed on 2026-08-07:

- after an unusually slow 98-second example-project run,
  `copy_n_segment_invariant.md` and `old_snapshot_loadable_after_free.md` each
  exhausted a smart tactic at almost exactly two seconds;
- after those two near-boundary proof sites were expanded, a parallel
  `cargo test` run timed out three unrelated verifier unit tests at almost
  exactly two seconds;
- all three unit tests passed immediately and consistently when rerun alone.

The affected unit tests were:

- `execute_until_expands_vector_storage_call_postconditions`;
- `explicit_store_step_with_unfolded_resource_facts_verifies`; and
- `resource_neutral_callee_preserves_callers_allocation_resource`.

This is broader than any one proof fixture. Continually expanding whichever
proof happens to lose the timing race would hide the unstable test boundary.

## Intended design

Production verification must still stop a slow tactic promptly. Correctness
tests must also continue detecting accidental unbounded search. However, a
hard correctness result should not depend on host throughput at a two-second
boundary.

Prefer a deterministic verifier-work budget for correctness enforcement, with
elapsed time retained for profiling and an outer wall-clock deadline retained
for hangs. If deterministic accounting is not yet practical, the interim test
design should isolate performance gates from semantic gates and apply an
explicit noise policy rather than silently raising every production limit.

Do not address this by raising the two-second smart limit, weakening fixtures,
or changing C source. Proofs that are intrinsically broad should still be
decomposed or expanded when that is independently the right proof design.

## Regression design

Add a test-only scheduling/load probe around a fixed smart proof and show that
its semantic result does not change when unrelated verifier tests run in
parallel. Separately verify that a deterministic exhausted-work fixture fails
with the ordinary bounded-search diagnostic and that an outer project deadline
still interrupts a hang.

The ordinary unmodified `cargo test` command—not a serialized or
budget-disabled variant—must be the acceptance gate.

## Acceptance criteria

- Repeated default `cargo test` runs remain green under ordinary parallel test
  execution and moderate independent CPU load.
- Correctness tests do not accept or reject a proof solely because the host
  completed slightly more or less work during two seconds.
- Production smart tactics still stop promptly and report the active proof
  site when their supported bound is exhausted.
- Profiling continues to report real elapsed/CPU timing, independently of the
  deterministic correctness boundary.
- No C fixture is reshaped and no global tactic duration is raised to make the
  regression pass.
