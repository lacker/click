# P1: Concurrency demo with thread ownership, mutexes, and publication

## Objective and violated invariant

Requested on 2026-09-15. Deliver basic concurrency support before launch,
alongside the selected basic-C++ milestone. Rbtree remains the main launch
demo. The intended additional claim is: **Click verifies memory safety, race
freedom, and functional safety properties of three small concurrent C
programs under one documented thread and memory-model profile.**

The purpose is to test the architecture early: thread-local proofs, resource
transfer, shared invariants, and synchronized observations must compose without
enumerating schedules or rewriting C into verifier-friendly sequential code.
A sequential proof must not authorize a concurrent access or preserve a
current-memory fact after another thread can invalidate it.

Three separate programs form one milestone. Disjoint workers alone would miss
shared mutation; mutexes alone would leave atomic publication untested. Each
program exercises a different boundary in the same production proof engine.
Small passing examples are necessary but insufficient evidence of scalability:
this milestone also requires modular rules and deterministic scaling tests.

## Existing foundation and scope

The first source-selection checkpoint is
[`design/concurrency-probes/fork_join.c`](../design/concurrency-probes/fork_join.c)
with its [profile record](../design/concurrency-probes/README.md). It fixes an
ordinary C11/POSIX program, compiler/target/API choices, and creation-failure
paths before any thread rule or sidecar is written. The fixture is deliberately
not yet listed as a verifying example; its source bytes are pinned by the
examples gate. The new user-space profile and pthread rules remain work for
this issue, not support already delivered by that checkpoint.

Build on the authority conservation, stable borrowing, observation support,
and checked transitions in the [stable-views record](../docs/internals/stable-views.md).
The two-context and mutex experiments in `src/kernel/tests/loan_model_tests.rs`
are design evidence only; they do not implement concurrent C semantics.

Before implementation, select and document one concrete C standard, supported
compiler/target configuration, thread/mutex API, and supported atomic subset.
Use a coherent C11-compatible account of ordinary accesses, data races, thread
start/join, mutex synchronization, and release/acquire publication. Bind the
profile and modeled API identities into imports, certificates, and caches.
Reject unsupported operations or orders locally. Never strengthen a source
atomic order silently or substitute sequentially consistent execution for a
weaker source program without a sound justification for the selected subset.

Thread and mutex library primitives may initially have explicit trusted runtime
specifications. Their resource and synchronization rules must still be checked
by the kernel, and all three client programs and their worker contracts must
be verified. Clearly distinguish verified clients from assumed runtime
implementations; proving an OS mutex implementation is outside this milestone.
Recognize the actual selected declarations, types, and macro/builtin lowering,
not arbitrary functions that happen to have matching names.

Pick small ordinary C sources, check that they exercise the intended patterns,
and freeze them before writing the sidecars. Preserve source and provenance in
the example projects. Synthetic examples are acceptable when identified as
such. Do not add proof-only locals, branches, helper calls, identifier changes,
or serial execution wrappers to make their proofs work.

## Three required programs

### 1. Fork/join over a partitioned buffer

A parent initializes a fixed-size buffer, starts two workers that modify
disjoint subranges, and joins them before reading the complete result.
Prove each worker's exact memory effect and the combined final contents.
Worker proofs must be modular and reusable independently of their scheduling.

Spawn transfers the worker's required authority out of the parent; a checked
completion handle allows join to recover its postcondition and returned
resources exactly once. Include a companion regression for shared read-only
borrowing across workers: the backing allocation and borrow remain live until
the corresponding shares return.

Reject overlapping write-authority transfers, parent access to transferred
memory before join, duplicate completion recovery, and freeing or leaving the
lifetime of borrowed storage while a worker can still access it. Account for
the selected API's thread-creation failure behavior: failed creation must not
fabricate a child or lose resources. Document any explicit runtime-success
assumption used by a demo and check its scope.

### 2. Mutex-protected counter

Two workers each increment the same ordinary counter once under one mutex.
After both joins, prove that the initially zero counter is exactly two and
that the accesses are race-free. Avoid overflow in the chosen scalar type.

The shared lock handle grants permission to use the protocol; it grants no
direct access to the payload. A successful acquisition obtains a unique guard
and the protected resources. Unlock requires restoration of the invariant and
returns the resources to the lock. Contributions or equivalent auxiliary
proof state must connect the two worker postconditions to the exact final
count; the weak invariant "the counter is nonnegative" alone is insufficient.
Keep this bookkeeping in Click, with checked conservation rules.

Reject an unguarded increment, access using the wrong mutex or an expired
guard, duplicate guard ownership, and unlock without restoring the invariant.
Add a regression that reads the counter, unlocks, then reacquires: an old
local value is still that old value, but cannot certify the current counter
without evidence that excludes intervening updates.

### 3. One-shot release/acquire publication

A producer initializes an ordinary payload, then release-stores a ready flag.
A single consumer acquire-loads the flag and reads the payload only after
observing the publication. Prove that this read sees the initialized payload.
Use a one-shot flag with explicit initial state and no resetting or reuse.
The consumer may poll, but the safety claim must not assume polling terminates.

The atomic protocol must relate the observed publication to the producing
write and its resource transfer. An acquire load does not gain arbitrary
published resources merely because it is labeled acquire. Transfer exclusive
payload authority at most once; repeated observations must not duplicate it.
Later uses can retain previously acquired authority where the protocol allows.

Reject the payload-read proof if either required release/acquire edge is
replaced with relaxed ordering, if the payload is read before observing ready,
or if the producer accesses the payload after surrendering its authority.
If relaxed accesses are initially unsupported, retain their local unsupported
diagnostics and add kernel counterexamples showing that absent synchronization
cannot establish the transfer. Do not describe unsupported syntax as a proved
data race. Include repeated-observation and competing-claim counterexamples
against duplicating the one-shot transfer.

## Required model and checked operations

- **Thread contexts and spawn/join:** distinguish concurrent components from
  alternative proof branches. Partition live authority and recover only the
  actual completed child's resources; never combine alternative histories as
  simultaneous ownership.
- **Lock invariants and guards:** represent resources held by a shared protocol
  outside any thread's usable context. Opening requires the matching
  synchronization operation and unique guard; ordinary resource unfolding
  cannot manufacture exclusive access to shared state.
- **Atomic initialization, load, and store:** preserve source types, supported
  orders, initialization, and distinct observations. Keep protocol access to a
  changing atomic cell separate from stable `views`; do not weaken the existing
  stable-borrow meaning or allow mixed ordinary/atomic access accidentally.
- **Observation and lifetime support:** preserve local copied values and facts
  about past snapshots, but require current authority and synchronization
  evidence for current-memory claims. Lock acquisition and publication must
  obtain supported observations rather than revive stale snapshot facts.
- **Certificates:** check synchronization, authority conservation, protocol
  identities, and permitted interference at the kernel boundary. Tactics and
  lowering propose transitions; they cannot assume another thread's result or
  certify one convenient schedule as covering every permitted execution.

Write down why each rule remains valid in the presence of arbitrary compatible
other threads, and why the selected memory semantics justify it. Reuse
sequential reasoning over exclusively owned or stable borrowed memory. Audit
call effects, frame transport, loops, and lifetime endings at the new boundary;
do not make every ordinary load enumerate other threads or invalidate the
entire project's memory state.

## Scalability and ordinary proof workflow

Follow the [verification efficiency contract](../docs/internals/verification-efficiency.md).
Use indexed thread, protocol, resource, and event identities with persistent
local updates. Explicit simple proofs must check in approximately linear work,
up to indexing factors, in selected source, proof, and certificate size.
Schedule enumeration, all-pairs interference checks, full-state clones per
transition, and scanning unrelated event histories are not acceptable designs.

Add deterministic work-counter regressions at four or more sizes for:

- increasing independent workers and disjoint resources;
- increasing lock or publication operations and their explicit certificates;
- fixed operations surrounded by increasing unrelated threads, protocols,
  facts, and historical observations.

Keep the simple-proof curves separate from bounded smart search. Document what
each measurement counts and any explicit output-dependent cost. Tiny examples
or faster warm timings alone do not establish this requirement.

Route all demos through normal verify, profile, expand, and audit using the
shared bounded engine. Establish ordinary verification before profiling or
expanding. Expanded sidecars must reverify against the original C. Diagnostics
must identify the access, missing authority or synchronization, and relevant
source locations within normal bounds. Follow `AGENTS.md` if tooling fails.

## Deferred support and acceptance criteria

General atomic read-modify-write operations (fetch-add, exchange, and
compare-exchange), reusable publication protocols, arbitrary relaxed atomics,
fences, condition variables, detached threads, lock-free data structures,
memory reclamation, Linux memory-model/RCU reasoning, and C++ threading remain
in [concurrency-and-atomics.md](concurrency-and-atomics.md). Avoid representation
assumptions that require every publication to be globally unique or every
thread count to be fixed at two; the first checked protocol can be narrow.
Do not claim deadlock freedom, eventual visibility, termination under arbitrary
scheduling, or lock-free progress. Functional postconditions apply when the
relevant operations complete; memory safety and race freedom cover execution
prefixes, including executions that do not complete.

Completion requires:

- All three original C programs, modular sidecars, profile assumptions, and
  reproducible commands are checked in; their stated safety and exact-result
  claims verify through the normal CLI.
- The negative regressions above fail for the intended local reason. Hostile
  certificates cannot duplicate authority, reuse expired identities, invent
  synchronization, or carry stale current-memory observations.
- A durable design record explains thread/protocol state, the memory-model and
  runtime trust boundary, rule justification, reused sequential rules, and
  extension points for the deferred atomic operations and protocols.
- Deterministic scaling curves pass; verify/expand/reverification/profile/audit
  agree; required positive and negative fixtures join the normal gate.
- Existing C and C++ regressions and `scripts/check.sh` pass. Documentation
  states the precise support claim and limitations. Delete this issue and its
  list entry when implementation, regressions, and durable documentation land.
