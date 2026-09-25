# Resource invariants, counting, and synchronization

This record specifies the target semantics shared by counted populations and
mutexes. It distinguishes the sequential implementation work from later
concurrent extensions. It is not a claim that Click implements Iris or that
the current mutex runtime has been validated against native pthreads.

## Semantic reference and implementation boundary

Use the ownership-transfer specification in the
[Iris lock lecture](https://iris-project.org/tutorial-pdfs/lecture11-cas-spin-lock.pdf)
for locks, and the authoritative counting and reclamation constructions in
[RustBelt Meets Relaxed Memory](https://plv.mpi-sws.org/rustbelt/rbrlx/paper.pdf),
especially section 3.3, for shared reference counting. Each added rule needs
an explicit interpretation in those constructions under the selected runtime
and memory model. Similar names are not a soundness argument.

The initial implementation remains a concrete, indexed checker. It does not
need arbitrary user-supplied resource algebras or all Iris modalities. A
primitive family supplies checked laws; declared resources compose primitive
and declared resources using ordinary containment, models, and conditions.
Both pass through the same contracts and resource interfaces. Runtime
operations have primitive authority-changing rules. Folding only packages
authority already owned; it cannot mint a guard, allocation, or counted unit.

Physical storage may remain in specialized indexed registries. Those registries
must agree with resource occurrences and must not independently duplicate
authority. Persistent data-structure copies represent alternative proof
states, not two concurrent owners.

Click's existing `core()` is a borrowing-description projection, not an
implementation of the Iris resource-algebra core. Stable `views` retain their
existing meaning: a borrow freezes its covered memory. A shared protocol
description must not be represented by a stable view of changing payload.

## Three separate components

1. **Membership:** independently owned units of a population.
2. **Authority:** the population's authoritative count and its one shared
   body, including memory and allocation obligations.
3. **Access protocol:** evidence permitting a context to access that body,
   together with the obligation to restore its assertion before releasing
   access.

For a population `R(a)`, write `unit(R(a), k)` for ownership of `k` units and
`total(R(a), n)` for the authoritative state. These are explanatory notation,
not new Click syntax. Units compose additively; zero supplies no access.
Moving units between callers, callees, parents, and workers leaves the total
unchanged. Creating or consuming units changes the authoritative count by a
checked update. Owning `k` units establishes that the total covers `k`; it
does not establish that the total is exactly `k`.

The interpretation must account for every outstanding unit, including units
inside other resources and suspended calls. Exact reclamation cannot rely on
an affine proof silently forgetting a unit. Explicit consumption and recovery
obligations remain part of Click's contract discipline.

`count(R(a))` denotes the population total at the selected proof snapshot.
It is not a runtime read and not an independently writable ghost variable.
For a shared population, learning its exact current value requires access to
the authoritative state or equivalent checked evidence. Historical equalities
remain facts about their snapshots, not permanent knowledge of current state.

## Closed assertions and exclusive opening

A population body describes its closed state. For example,
`obj->refs == count(child_ref(obj))` relates owned C memory to the total at a
closed boundary. It need not hold after every statement inside an authorized
update. The body has exactly one usable representation: closed in its
protocol, or open in the holder's resource context.

Opening consumes or suspends the access authority and yields the body plus a
unique restoration obligation. Closing requires the actual body resources
and its facts at the new count and memory snapshot. It discharges that
obligation and restores access authority. No sibling unit, nested open,
callback, contract entry, or observation may independently re-project the
closed assertion while it is open. Helpers may operate on explicitly passed
pieces of the open body, subject to ordinary ownership and borrowing rules.

There are three access disciplines:

| Discipline | Permission to open | Closing boundary |
| --- | --- | --- |
| Sequential population | Exclusive authority tied to its execution domain | End of the checked update/open scope |
| Lock-protected population | Current thread's live guard | Before unlock |
| Atomic population | The selected atomic protocol's accessor | The protocol's justified atomic update |

Sequential access may be implicit surface syntax, but its authority and
open/closed state must be checked. It is not granted independently by every
unit. Stateful sequential populations remain thread confined, transitively
through containing resources. Confinement alone does not discharge the
same-thread reentrancy obligation.

An ordinary folded resource may continue to project facts supported by its
owned body. A population member instead refers to a shared body: observing
its facts must check that body's access protocol and closed state. Neither
the word `fact` nor positive quantity supplies synchronization.

## Count transitions at calls and returns

Passing a unit into a function is a transfer, not destruction. A `consumes`
clause specifies a net population decrease; `produces` specifies a net
increase. A verified retain/release implementation must justify the physical
update and the logical update together at an authorized closing boundary.

A modular call applies that verified effect once. Its evidence identifies the
population, predecessor count, successor count, resulting body assertion,
and relevant memory/resource support. The enclosing function's certification
checks its actual returned state against its own net contract; it must not
apply a nested call's population delta a second time.

Returned transition obligations are proof obligations, never facts merely
because a transition was constructed. A flag saying a transition was checked
is valid only after all its obligations have been discharged. Adding an
unrelated pure postcondition must not change this rule.

A consuming call can leave a nonempty population although its caller returns
no local unit. The remaining population's invariant still has to hold. Zero
local units therefore cannot justify skipping restoration. Conversely, sound
evidence established by the call must survive later disjoint writes through
the existing memory-support rules. Potentially aliasing writes invalidate
that transport. Deallocation discharges the allocation obligation only at
the checked final-release transition.

## Composable mutex resources (subsequent implementation)

Separate the persistent description of a lock's protocol from its live-use
permission, thread-owned acquisition guard, and protected assertion `I`.
The description identifies a storage lifetime and protocol generation; equal
addresses after destruction/reinitialization do not identify one protocol.

For the supported nonrecursive mutex profile:

- Initialization requires exclusive live mutex storage and `I`, deposits
  `I`, and establishes lifecycle authority.
- Lock requires live-use permission and no current guard held by this thread.
  On successful completion it yields a fresh guard and current resources
  satisfying `I`. The caller need not prove global unlockedness. This rule
  does not prove termination or fairness.
- Unlock requires this thread's current guard and restored `I`, with no live
  borrowers of returned memory. It consumes both and returns `I` to the
  protocol.
- Destruction requires exclusive lifecycle authority, no guard, and recovery
  of all participation rights, including those of possible waiters. It
  retires the protocol and recovers `I`; freeing storage is a separate step.

Guards are ordinary exclusive resource ingredients. A declared model may
contain a guard in its `Holding` arm and no guard in its `Idle` arm. Function
contracts may return a guard on the same thread; pthread guards cannot be
transferred to a different thread. A loop proves the same conditional
ownership assertion at its backedge, not equality of acquisition epochs.
The parity probe relates the model to index parity. A false parity relation
cannot manufacture the missing guard.

## Shared accounting and reclamation (subsequent implementation)

For the mutex counter, conserved pending and completed units can satisfy
`pending + completed = 2`, with `counter.value == completed` inside the
protected assertion. Each worker's C increment and unit conversion restore
that assertion before unlock. Join returns the worker's contribution;
neither spawning nor joining invents or destroys population units.

Reference counting uses the same membership accounting with a different
body. A reference may justify a lifetime claim and immutable payload access
only through the chosen protocol. It never implicitly grants mutable access
to the payload. Final release must establish absence of outstanding users
and loans and recover allocation authority. Atomic decrement to zero alone
does not establish the required ordering of earlier payload accesses.

The frozen sequential shared-parent source remains the sequential regression.
A lock-protected companion and an atomic companion are separate programs;
their proofs cannot be inferred from the sequential proof. Atomic reclamation
must use a construction appropriate to the selected weak-memory semantics,
not the sequentially consistent tutorial invariant rule applied unchanged.

## Migration and acceptance

First establish sequential access and certification, retaining thread
confinement. Require the tautological-ensure regression, unchanged shared-parent
lifecycles in both orders, and rejection of wrong count updates, duplicate
authority, nested access while open, and premature reclamation. Preserve
checked facts across disjoint writes and reject aliasing transport.

Then integrate guards into ordinary resource composition and verify wrappers,
same-thread contract transfer, and the unchanged parity loop. Shared mutex
participation and interference follow; exact concurrent counting follows
that. Atomic reference counting is a later memory-model extension.

Every implemented checkpoint needs focused positive and hostile tests and
the full `scripts/check.sh` gate. Changed representations need deterministic
multi-size work regressions. Checking one selected population or guard must
touch its indexed support and explicit delta, not scan unrelated populations,
protocols, threads, or history. Verification, expansion/reverification,
profiling, and audit must agree at each completed example checkpoint.

## Implemented checkpoint and remaining work

The first checkpoint enforces the counted body's invariant before a modular
call may observe it, including a call made inside `open`. Restoring the
invariant permits a sequential helper call; this is a checked boundary, not
independent authority for a second observer. Ordinary folded resources are
unchanged: their bodies remain inside their heads. The explicit access token
and suspension model described above is still future work, particularly for
nested access and concurrency.

The surface's return-resource adapter now checks the obligations returned by
the kernel before marking its transition checked. Calls involving counted
bodies retain checked ownership-partition evidence for exposed memory and
the caller's frame. This lets certification transport the returned count
invariant across a disjoint parent-link store. The shared-parent helper with
a tautological additional postcondition now verifies.

Initialization is now explicit in the shared body: `defined(obj->refs)` and
`defined(obj->payload)` promise valid typed reads, while the count equality
only relates values. The parent resource likewise promises a defined child
pointer. Opening these facts checks ownership or a live loan dependency;
the facts themselves grant neither access nor thread safety.

Contract certification transports initialization only along checked memory
steps that leave the typed range unchanged, with unchanged lifetime metadata.
The walk stops at the named premise's snapshot rather than traversing its
earlier history. A failed allocation now records its no-write memory edge,
so allocation-failure cleanup can retain a preceding initialization guarantee.
`population_initialized_cleanup.md` verifies this complete lifecycle. The
older `shared_heap_population_initialized_body_gap.md` now documents the
intentional rejection when the resource omits initialization guarantees.

Unknown pointer values read from heap or temporary storage now receive opaque
identities, including reads from materialized load-variable cells. They cannot
inherit the fresh block identity of the object storing them: a parent's child
pointer can target a different allocation. Known stored pointers keep their
actual target. `heap_pointer_field_keeps_target_identity.md` and its negative
counterpart check a modular store/read boundary; the kernel regression covers
both logical and checked typed reads. This repairs a pointer-identity boundary
encountered while proving the caller; it does not complete payload transport.

The complete shared-parent callers remain unfinished.
`shared_heap_population_payload_frontier.md` preserves the unchanged C and a
complete first-removal caller proof that reaches `out == payload`; the
remaining failure concerns payload/alias transport across detach and read.
Finish both caller proofs before claiming the sequential migration complete
or proceeding to shared mutex integration. No mutex runtime or concurrent
reclamation rule changes in this checkpoint.

All six shared-parent helper claims pass the complete 18-site expansion
and independent-reverification audit. Path completion performs the checked
return-resource exchange after open bodies and deferred invariants have been
restored, even when simple tactics close every pure claim and no resource is
returned. This removes the dependence on a final `simp()` to discharge the
nonfinal release's allocation-lifetime obligation. The regression
`shared_population_release_expansion_retains_lifetime` verifies, expands,
and independently reverifies the unchanged C and helper proof. A final
release that omits `free` is still rejected with a simple closer.
