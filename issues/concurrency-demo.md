# P1: Verify representative concurrent C programs

## Goal

Show that Click can verify useful properties of ordinary concurrent C, not just
parse pthread declarations. For the supported C11 subset and a named runtime
binding, a proof must establish memory safety, freedom from conflicting
unsynchronized accesses, and an exact functional result when the operations
complete. The same checked authority and observation rules must cover three
different ways threads interact:

1. **Fork/join:** workers own disjoint writable ranges and share stable input.
2. **Mutex:** workers mutate the same ordinary cell through one lock invariant.
3. **Release/acquire:** a consumer observes a producer's one-shot publication
   before reading an ordinary payload.

These examples test independent boundaries. Disjoint workers alone do not
exercise shared mutation; a mutex alone does not exercise atomic visibility.
The verifier must not prove one convenient schedule and treat it as all
schedules. Safety claims apply to execution prefixes, including ones that
never complete. Exact-result claims may rely on the relevant operations
completing; they do not imply fairness, deadlock freedom, or termination of a
polling loop.

## Current state

The unchanged [fork/join C program](../examples/concurrency-fork-join/fork_join.c)
and its [sidecar](../examples/concurrency-fork-join/fork_join.click) verify in
the normal gate under an explicitly selected **modeled pthread runtime**. The
proof transfers two disjoint output slices to workers, lends their stack job
records as stable views, and recovers each child's resources and postconditions
only at its matching join. It covers both successful creates, first-create
failure, and second-create failure with cleanup. The successful output is
[11, 11, 22, 22]; the two failure outputs are [0, 0, 0, 0] and
[11, 11, 0, 0]. Shared-reader companions cover both join orders, failed
creation, and recovery of explicit, implicit stack, and owned backing.
Hostile regressions reject overlapping writers, parent access before join,
duplicate or wrong-child recovery, and premature lifetime end.

This is a conditional client proof. Click checks the client and the
create/join authority transitions against a trusted modeled pthread
specification; it has **not** established that a native Linux or macOS
pthread library matches that specification. The compiler-import path locks a
real Ubuntu GCC/glibc artifact for the frozen source, but header parsing
currently stops at weak linkage on `__pthread_unwind_next` in `pthread.h:753`.
Importing declarations by itself would not validate
runtime behavior.

The mutex counter, release/acquire publication, and native pthread binding
remain open. [The probe record](../design/concurrency-probes/README.md)
describes the selected source and profile; [the binding design](../design/concurrency-probes/pthread-binding-design.md)
records the existing create/join rule and trust boundary.

## Remaining work

### Native pthread binding

For each platform on which we claim the verified C program runs, connect the
modeled operation to the actual selected declarations, ABI, and runtime
semantics. The first intended profile is Debian Bookworm GCC 12/glibc 2.36,
C11, x86-64 Linux user space, LP64, with the compile options in the probe
record. The current Ubuntu GCC 13/glibc 2.39 artifact is a parser regression,
not validation of that profile.

A complete real-header import or a separately designed checked declaration
projection could establish declaration and ABI identity. Either way, the
binding must name the trusted runtime specification and reject mismatched
headers, types, options, or same-named lookalike functions. Advance the frozen
import's bounded refusal without changing the C source or silently treating a
modeled result as a native one. A macOS claim would need its own target, SDK
checks, runtime binding, and artifact identity.

### Mutex-protected counter

Freeze a small ordinary C program before adding its sidecar. Two workers each
increment the same ordinary counter once under one mutex. Starting from zero,
prove the final count is exactly two after both joins and that all counter
accesses are protected.

A shared lock handle grants permission to use a protocol, not direct access
to its payload. Successful lock acquires a unique guard and the protected
resources; unlock checks that the invariant has been restored and returns
them. Checked contribution accounting, or an equivalent conserved ghost
state, must justify the exact final count. A weak invariant such as
"counter >= 0" does not suffice.

Reject an unguarded increment, access under the wrong or expired guard,
duplicate guard authority, and unlock without restoring the invariant.
After unlock and reacquire, an earlier local copy remains a fact about that
copy but cannot stand in for the current counter value. Model lock failure or
restrict the supported API with an explicit, checked assumption.

### One-shot release/acquire publication

Freeze a C11 program in which a producer initializes an ordinary payload and
release-stores a ready flag. A consumer acquire-loads the flag and reads the
payload only after observing the publication. Prove that this read sees the
initialized value. The flag starts in a stated initial state and is published
once; polling need not be proved to terminate.

A matching acquire observation must be tied to the actual release event and
its resource transfer. Labeling a load "acquire" alone grants no payload
authority. The protocol transfers exclusive payload authority at most once;
repeated observations and competing consumers cannot duplicate it. Reject
reading before observing ready, producer access after surrendering the
payload, and a proof with either required ordering edge weakened to relaxed.
If relaxed operations are outside the first supported subset, refuse them
locally and use kernel counterexamples to show why the transfer cannot be
inferred without synchronization.

## Required proof boundary

- **C and runtime identity:** state the supported C11 ordinary-access,
  data-race, thread-start/join, mutex, and release/acquire semantics. Recognize
  exact selected declarations and operations. Bind the target, import/profile,
  and trusted runtime specification into proof artifacts and caches. Reject
  unsupported orders and operations; never strengthen source ordering
  implicitly.
- **Authority:** keep writable ownership exclusive across concurrent
  contexts. A live completion right belongs to one actual child and is
  consumed once. Lock-protected and published resources live in checked
  protocols while unavailable to ordinary thread contexts. Stable views
  cannot authorize reads of changing lock-protected or atomic memory.
- **Observation:** preserve facts about copied locals and past snapshots, but
  require current authority and synchronization evidence for current-memory
  claims after another thread may interfere.
- **Certificates:** the kernel checks authority conservation, protocol
  identities, synchronization, and allowed interference. Lowering and tactics
  may propose transitions; they cannot invent an observation or assume the
  result of another thread. Reuse sequential reasoning on exclusively owned
  or stable borrowed memory without enumerating schedules.

The [stable-views record](../docs/internals/stable-views.md) and current
fork/join rules are the starting point. Implement the lock and publication
protocols through ordinary C execution and the shared bounded verification
engine. Keep the C source fixed when proof work exposes a Click gap.

## Acceptance

- All three frozen C programs and modular sidecars verify through normal
  verify, profile, expand/reverify, and audit workflows under one documented
  memory-model profile. Their stated safety and exact-result properties hold
  at the supported boundary.
- Positive and hostile regressions cover the authority, synchronization,
  stale-observation, failure, and duplicate-recovery cases above. Forged
  certificates cannot bypass a checked transition. Diagnostics identify the
  relevant source access and missing authority or synchronization.
- Deterministic work-counter tests cover increasing independent workers,
  increasing lock/publication operations, and fixed operations amid growing
  unrelated threads, protocols, and history. Explicit simple proofs scale
  approximately linearly up to indexing factors; no schedule enumeration,
  full-state clone per step, or unrelated-history scan.
- A durable design record justifies each concurrent rule under arbitrary
  compatible threads and states the runtime trust boundary, supported orders,
  and deferred extensions. The full scripts/check.sh gate passes.

General read-modify-write atomics, reusable publication, fences, condition
variables, detached threads, lock-free structures, reclamation, and C++
threading remain in [broader concurrency support](concurrency-and-atomics.md).
Exclusive transfer of implicit stack/global/static storage is also deferred;
the fork/join demo needs stable stack views, not that transfer. Delete this
issue and its index entry when the three programs, binding claims, tests, and
documentation satisfy the acceptance criteria.
