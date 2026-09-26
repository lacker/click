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
real Ubuntu GCC/glibc artifact for the frozen source. That artifact now loads
through the ordinary import path on macOS, including the real header
declarations, and verifies the unchanged worker and parent sidecar against the
trusted modeled pthread runtime. The proof records the locked import identity
and remains conditional on that runtime specification; it does not validate
native runtime behavior.

The concurrent mutex counter, release/acquire publication, and native pthread
binding remain open. The [mutex counter C source](../design/concurrency-probes/mutex_counter.c)
is now frozen; its [shared-protocol design](../design/concurrency-probes/mutex-shared-protocol.md)
records the required authority rules. [The probe record](../design/concurrency-probes/README.md)
describes the selected source and profile; [the binding design](../design/concurrency-probes/pthread-binding-design.md)
records the existing create/join rule and trust boundary.
The resource-body spelling `guarded_by counter->mutex;` now binds a folded,
exclusive instance to a typed `pthread_mutex_t` member. A single C path can
initialize that mutex with an explicit resource selection, lock to retrieve
the resource, restore it before unlock, and destroy the mutex to recover it.
The [C proof fixture](../mdtests/guarded_resource_mutex_flow.md) exercises
this flow and rejects a wrong mutex and an unfolded unlock. The runtime model
assumes these valid calls succeed. Worker sharing and interference rules are
still needed before this proves the concurrent counter.

### Mutex model boundary

`held(&mutex)` is a checked fact about the current path's guard. Straight-line
lock/unlock and loops that restore the same mutex ownership at every loop
head verify. The [quarantined parity probe](../design/concurrency-probes/mutex_held_parity.c)
is ordinary C that alternates lock and unlock according to the loop index,
then releases any final guard and destroys the mutex. It has no Click sidecar
or passing proof. At its loop head, whether the guard is held depends on the
index parity. The current loop state has one concrete mutex status, so the
backedge cannot express that relation for arbitrary `n`.

The next mutex-state design needs a checked conditional guard state: establish
its relation to `i` at entry and on every backedge, narrow it on each branch,
and never manufacture unlock authority at a join. It should reject a false
parity claim and an unlock on a path without the guard. Mutex lifecycle also
needs an explicit connection to the storage holding `pthread_mutex_t`:
initialization and destruction are separate from allocation and freeing, and
the current ledger does not establish that the storage remains live for every
initialized mutex. Returning a held guard is currently refused; a design for
transferring it through a function contract remains open. These are distinct
from the shared lock protocol required by the concurrent counter.

## Remaining work

### Native pthread binding

For each platform on which we claim the verified C program runs, connect the
modeled operation to the actual selected declarations, ABI, and runtime
semantics. The first intended profile is Debian Bookworm GCC 12/glibc 2.36,
C11, x86-64 Linux user space, LP64, with the compile options in the probe
record. The current Ubuntu GCC 13/glibc 2.39 artifact is an offline proof
regression, not validation of that profile.

The locked Ubuntu import checks the selected declaration origin and types for
the conditional modeled proof. A native claim additionally needs ABI and
runtime evidence that the selected pthread implementation meets the trusted
runtime specification, with a pinned platform profile. The binding must
reject mismatched headers, types, options, or same-named lookalike functions.
A macOS claim would need its own target, SDK checks, runtime binding, and
artifact identity.

### Mutex-protected counter

The C program is frozen before its sidecar. Two workers each increment the
same ordinary counter once under one mutex. Starting from zero,
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

### Guard ownership checkpoint

Modeled lock acquisition now supplies an opaque exclusive guard atom in the
ordinary resource context. Unlock consumes that exact acquisition's atom;
ledger heldness alone, a stale guard, a view, or a counted quantity cannot
supply ownership. The guard is thread-confined and grants no memory access
on its own. Kernel regressions cover missing/stale authority, invalid
composition, consumption, and logarithmic indexed work amid unrelated guards.

The surface now supports `owns mutex_guard(mu)` in declared-resource bodies,
including conditional model arms. Guard-bearing contracts (including wrapped
guards) are refused until abstract entry protocol state is available: a
hostile helper must not reinitialize a mutex while preserving a guard wrapper.
Ordinary calls with live protocols are refused until contract effects track
them, and argument binding retains the ledger instead of erasing it. Direct
guard contract inputs/outputs also need abstract entry protocol state;
lock-changing helpers and loop joins across acquisition epochs remain open
before the unchanged parity loop can verify. Protocol lifecycle and shared
interference are also still open.

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
