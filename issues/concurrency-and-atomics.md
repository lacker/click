# Model concurrency and atomics

Priority: P2.

Soundness: incomplete. Concurrency beyond fork/join, mutexes and one-shot
publication is refused. For example, `#include <stdatomic.h>` with
`atomic_fetch_add` is rejected at include processing under the default
target. The modeled pthread interface is a documented trusted specification
in `docs/concepts/trust.md`, not an open gap of this issue.

Proofs are stated against Click's own `<pthread.h>` and `<stdatomic.h>`
interfaces and their [trusted specification](../src/languages/c/modeled_pthread_spec.md).
This issue owns concurrency support beyond fork/join, mutexes, and one-shot
release/acquire publication, including general atomic read-modify-write operations, reusable
protocols, additional orders/fences and synchronization APIs, reader/writer locks,
detached threads, lock-free structures, and concurrent memory reclamation.
Future C++ threading is also in scope: keep the shared task and completion
model independent of pthread's result codes and handle storage,
with checked adapters for moves, captures, exceptions, and cleanup joins. The
[accepted binding design](../design/concurrency-probes/pthread-binding-design.md#future-c-threading)
records these extension constraints; implementing C++ threading is not a P1
pthread prerequisite. The atomic-counter regression below remains a follow-up;
the P1 counter uses a mutex and ordinary memory.

The [stable views record](../docs/internals/stable-views.md) establishes stable shared borrowing
and checks resource transfer between small modeled thread contexts. Build on
those resource laws here; this issue owns the C execution/memory model,
synchronization, and atomics needed for production concurrency support.

A mutex-protected dynamic collection first needs the ordinary-resource
composition work in P1. Condition variables additionally need a checked
release/wait/reacquire protocol; reader/writer locks need shared-reader
authority; detached threads need lifetime reasoning beyond a matching parent
join. Lock-free algorithms need atomic interference and abstract-operation
reasoning, while reclamation must establish that no thread can still access
retired storage. These are semantic extensions, not features obtained merely
by accepting additional API names.

Deadlock freedom, fairness, and termination are separate proof goals. The
current safety model does not establish them. Do not silently strengthen a
safety claim into a progress guarantee.

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
