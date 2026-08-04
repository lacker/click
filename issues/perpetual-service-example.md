# Add a perpetual-service example

## Dependency

Add this example after partial-correctness kernel cleanup and divergence-aware
function certification. Existing opaque call summaries should then verify its
core behavior without inventing a return; recursive C support is not required.

## Why this example

The first larger example for divergence should be small enough to expose the
proof model rather than simulate an operating system. A useful project shape is
a perpetual service that owns composite state and repeatedly calls one verified
step function:

```c
int32 service_run(struct service *service) {
    int32 status;
    while (1) {
        status = service_step(service);
    }
    return 0;
}
```

The service resource can own a phase field and a small backing cell. A
nontrivial `service_step` toggles or advances between two safe protocol states,
returning the same folded composite resource. The loop invariant owns that
resource and records the phase bounds. `service_run` has no return frontier but
is safe for every finite number of iterations.

This exercises several interactions that isolated scalar mdtests do not:

- a verified opaque call inside a perpetual loop;
- repeated transfer and return of a composite owned resource;
- loop invariant preservation across fresh call-summary memory identities;
- absence of a function return frontier; and
- a visible distinction between safety and termination.

Prefer the directory name `perpetual-service`. It says what is unusual about
the project without promising external I/O semantics that Click does not have.

## Proof expectations

- `service_step` has an ordinary terminating contract and proves that it
  preserves the service resource and legal phase states.
- `service_run` proves body safety and loop-invariant preservation under the
  partial-correctness model.
- The example must not add a fake loop bound, fuel parameter, or unreachable
  environmental assumption merely to make certification find a return.
- The example must not claim that steps continue to occur forever. Absence of
  UB on every finite prefix is a safety theorem, not a scheduler fairness or
  productivity theorem.

If a natural variant can optionally stop, include a separate `service_until`
function whose `ensures` clauses demonstrate that postconditions apply on its
return branch. Keep the unconditional perpetual function as the central case.

## Why not a stream processor yet

A convincing stream processor needs a way to model an external input action
and state a property of the resulting event history. Click currently has no
trace values, I/O events, environmental fairness assumptions, or guarded
productivity judgment. Encoding a finite input array would only produce a
terminating cursor example, while using an unconstrained helper would disguise
the missing environment semantics behind an opaque call.

Do not add a large stream example until Click can state at least a prefix-safety
property such as “every emitted output is a legal response to the preceding
input trace.” Liveness—such as eventually processing every input—should remain
a separate later design.

## Acceptance criteria

- `examples/perpetual-service/` contains C, Click, and a candid README.
- The example verifies through the normal directory example test.
- It uses a composite resource and an opaque verified step call inside a
  constant-true loop.
- No proof object or documentation claims that `service_run` returns.
- The README explains exactly what is proved over finite prefixes and what is
  not proved about progress, traces, or fairness.
- At least one focused mdtest already covers each foundational behavior, so the
  example is illustrative rather than the only regression test.
