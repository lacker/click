# Resource invariants, counting, and synchronization

This record specifies the target semantics shared by counted populations and
mutexes. It distinguishes the sequential implementation work from later
concurrent extensions. It is not a claim that Click implements Iris or that
the current mutex runtime has been validated against native pthreads.

The [concurrency contract proposal](concurrency-contracts-and-diagnostics.md)
sets out the candidate surface clauses, lifecycle/use permissions, and
program-level failure explanations for human review. Its unresolved choices
are not additions to the implemented language.

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

Sequential `open` now records suspended access separately from membership.
Each opening has a fresh restoration identity and an indexed active-scope
set. A second open or finalizing unfold of the same population, including a
proved pointer alias, is rejected. Scopes close in order only after the body
resources and assertions are restored; closing recovers the exact preceding
authority state. Branch copies represent alternative states, not additional
owners. The kernel checks each selected access transition alongside the
resource rewrite, and state comparisons retain the access state.

A modular call cannot obtain the suspended body through a population clause,
even if the current memory happens to satisfy its invariant. Close the scope
before calling such a helper, or pass explicit owned/borrowed body pieces.
The positive and hostile `population_call_*`, `population_open_calls_explicit_piece`,
and nested-open fixtures cover these alternatives. Deterministic multi-size
checks bound the scope index updates logarithmically and restoration by a
constant-time return to the preceding authority state. Resource artifacts
use a new semantics version so earlier certificates cannot bypass this rule.

This checkpoint supplies sequential suspension and restoration. The following
mutex checkpoint puts acquisition guards in the ordinary kernel resource
context as `CResource::MutexGuard`: an opaque acquisition identity with one
exclusive owned unit, no view, no count splitting, and no memory authority.
Acquiring creates the atom alongside the protected assertion. Unlock consumes
the current acquisition's atom as well as the restored assertion. The ledger
still describes protocol state; its held bit cannot recreate absent ownership.
Stale guard atoms do not authorize a later acquisition, and direct worker
transfer rejects guards as thread-confined. Indexed validity and deterministic
multi-size acquisition/release tests cover unrelated held guards.

The surface now lowers `owns mutex_guard(mu)` to a dedicated
`CResourceTerm::MutexGuard`, with explicit pointer snapshot selection. It
resolves the current acquisition identity; folding must separately consume
that atom from the available resources. Guards compose in ordinary exclusive
resource bodies and conditional model arms. Guard-containing definitions and their transitive
wrappers are thread-confined and marked as guard-bearing for contract checks.
Both function argument binders retain the caller's mutex ledger. Preserving
owned instance inputs containing guards additionally freeze mutex transitions
for the checked body. This boundary is carried in C state, substitution, and
state equality; nested calls cannot erase it. Returning across it retains the
caller's acquisition and restores the caller's transition permissions.

Preserving helpers can unfold guard instances using a symbolic acquisition
associated with the mutex pointer. This symbolic form is restricted to abstract
entries without a concrete mutex ledger and with every mutex transition frozen.
Evaluating a guard term describes a required resource; only checked unfolding
of an owned body supplies it. Folding consumes it. An exposed guard establishes
`held(mu)`; absence of an exposed guard does not establish `not held(mu)`.
Symbolic atoms remain distinct from concrete acquisition epochs. A concrete
preserved guard requirement selects the entry acquisition, even if a later
state contains a replacement acquisition at the same address. Direct
`owns mutex_guard(mu)` clauses now use this rule: abstract entry construction
assumes the atom and freezes protocols before resource evaluation, while calls
must supply checked ownership. The ordinary owned-borrow transfer retains the
entry atom for return. Concrete atoms retain their acquisition address for
source-level missing-resource diagnostics; that address is immutable provenance,
not a variable that changes acquisition identity during substitution. Named
primitive binders and consumed/produced guards remain refused. Calls with live protocols require a preserving
guard input; suspended workers remain refused. All modeled mutex transitions
reject a preserving body, even when its abstract entry has no concrete ledger.
The reinitializing, unlocking, destroying, and nested-reset helper fixtures
protect this boundary. Opaque entry heldness is not interpreted as false.

Every successful modeled initialization now has a fresh internal identity,
independent of the mutex address and protected resource. Lock/unlock retain
that identity; destroy/init replaces it. Concrete release witnesses must match
both the initialization and acquisition. Loop joins compare initialization
identity for the changed mutexes, so depositing the same protected instance
at the same address cannot disguise a replacement. A mutex created and
destroyed entirely within an iteration leaves no loop-head obligation.
The loop checker reports replacement of a loop-head initialization as an
unsupported contract, not as evidence that the C program is incorrect.
The lifecycle ownership checkpoint below exposes this identity as `mutex_live`;
use loans and full storage-lifetime checks remain open.

Heap retirement now checks an index of initialized mutex footprints. The
modeled binding supplies the complete ABI storage extent, retained through
lock/unlock and removed on destruction. Direct free/realloc and allocation
retirement at verified calls use the same check, including contracts whose
allocation continuity is unknown. Lookup visits only footprints in the affected
symbolic block; unrelated concrete blocks incur no scan. Ambiguous same-block
overlap requires checked separation. Abstract preserving helpers cannot yet
retire allocations, since their lifetime dependencies lack checked inputs.
This does not yet reserve mutex bytes against writes, validate their initial
storage, or handle automatic-storage expiry.

The lifecycle owner now lives in the same resource context as guards, as
`CResource::MutexLive`. Initialization mints exactly one owned atom; destruction
consumes the atom for that initialization. Acquiring currently requires that
owner too, until a checked `mutex_use` loan can authorize it instead. Folded
owners cannot authorize either transition until unfolded. The exclusive
resource algebra refuses duplicates, views, and counts; it implies neither
memory authority nor heldness. Generation identity survives lock/unlock and
cannot be renamed through concrete pointer substitution. Missing ownership
uses `Requires owns mutex_live(...)`.

Direct preserving `owns mutex_live(mu)` contracts and field-bearing wrappers
use the same entry-snapshot transport and abstract-protocol freeze as guards.
The shared mutex-authority validity index tracks only duplicate or malformed
atoms. Multi-size tests exercise initialization/destruction amid unrelated owners.
These facts do not yet justify worker transfer, lifecycle replacement at calls,
or a claim that initialization storage has been checked. Checked use lending,
reborrowing, guard holds, and join recovery remain the next semantic boundary.

Direct named primitive guard/lifecycle binders, lock-changing contracts, loop joins
across acquisition epochs, borrowed lifetime authority, and
shared interference remain later work. This checkpoint does not add
concurrent population access.

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
encountered while proving the caller.

The attachment contract now exports `p->kid == kid` as well as the abstract
`ParentLink::Linked(kid)` state. A caller can retain this pointer identity at a
named snapshot and establish the detach contract's count guard. The lifecycle
regression checks that both the recorded identity and conditional payload
preservation are available after detach. Neither pointer equality nor a
membership count grants access to the body.

Both complete shared-parent callers now verify against the unchanged C.
`shared_heap_population_lifecycles.md` covers both parent destruction orders,
allocation failures, the surviving parent's payload, and final reclamation.
Pointer rewriting uses a registered load's observed execution snapshot rather
than its projected identity snapshot, retaining the history needed to connect
equal addresses. The focused `rewrite_heap_alias_after_modular_call.md`
regression passes; its negative counterpart rejects an overwritten payload.

Population transitions now resolve their resource arguments to the same
checked ledger identity as Count observations. Previously, consuming
`child_ref(parent->kid)` could create/remove an alias entry while leaving
`child_ref(kid)` active, so certification demanded its initialization after
free. Quantities are aggregated under the proved identity before calculating
the transition delta. Unproved aliases and distinct children remain separate;
aggregated aliases still undergo the count-overflow check. This changes
accounting, not the requirement to restore every remaining population's body.

All eight claims pass the complete 42-site expansion and independent
reverification audit. Composable mutex access authority and mutex
integration remain later work; this checkpoint proves sequential lifecycles,
not concurrent reclamation.

Path completion performs the checked
return-resource exchange after open bodies and deferred invariants have been
restored, even when simple tactics close every pure claim and no resource is
returned. This removes the dependence on a final `simp()` to discharge the
nonfinal release's allocation-lifetime obligation. The regression
`shared_population_release_expansion_retains_lifetime` verifies, expands,
and independently reverifies the unchanged C and helper proof. A final
release that omits `free` is still rejected with a simple closer.
