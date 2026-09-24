# Model concurrency and atomics

Click verifies a frozen concurrent C fork/join program under an explicit
modeled pthread runtime. Native runtime validation, mutexes, and atomics
remain open. See the [P1 concurrency milestone](concurrency-demo.md#current-state)
for the current boundary and remaining three-program acceptance criteria.

The P1 [concurrency demo](concurrency-demo.md) owns the before-launch slice:
three programs exercising fork/join ownership, mutex-protected mutation, and
one-shot release/acquire publication, with production checked rules and
deterministic scaling regressions. This P2 issue owns broader support beyond
that slice, including general atomic read-modify-write operations, reusable
protocols, additional orders/fences and synchronization APIs, and concurrent
memory reclamation. Future C++ threading is also in scope: keep the shared task
and completion model independent of pthread's result codes and handle storage,
with checked adapters for moves, captures, exceptions, and cleanup joins. The
[accepted binding design](../design/concurrency-probes/pthread-binding-design.md#future-c-threading)
records these extension constraints; implementing C++ threading is not a P1
pthread prerequisite. The atomic-counter regression below remains a follow-up;
the P1 counter uses a mutex and ordinary memory.

The [stable views record](../docs/internals/stable-views.md) establishes stable shared borrowing
and checks resource transfer between small modeled thread contexts. Build on
those resource laws here; this issue owns the C execution/memory model,
synchronization, and atomics needed for production concurrency support.

## Violated invariant

Click should not certify a concurrent C program using sequential reasoning that
can hide a data race, reorder an atomic access, or miss a synchronization
failure.

## Intended regression

An unchanged two-thread C fixture uses an atomic counter and a release/acquire
flag. A race-containing variant must be rejected, while the synchronized
variant receives a contract whose memory observations match the selected memory
model.

## Acceptance criteria

- The supported memory model, atomic orders, thread creation/join, and race
  diagnostics are documented and represented in the kernel.
- Proof rules prevent sequential proofs from being reused across unsound
  concurrent transitions.
- The synchronized and racy regressions pass; `scripts/check.sh` passes.
