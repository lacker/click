# Resource invariants, counting, and synchronization

This is the design record for resource invariants and mutex-protected
resources. Populations use explicit authority instead: `authorized` families
with bodyless members governed by `authority(...)`, whose controls state the
population's facts. The
[authority establishment review](authority-establishment-review.md) and the
[worker authority protocol](worker-authority-protocol.md) describe that model.
A protected mutex resource comes only from its checked initialization.

This record is not a claim that Click implements Iris or that the mutex
runtime has been validated against native pthreads.

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

The implementation is a concrete, indexed checker. It does not
need arbitrary user-supplied resource algebras or all Iris modalities. A
primitive family supplies checked laws; declared resources compose primitive
and declared resources using ordinary containment, models, and conditions.
Both pass through the same contracts and resource interfaces. Runtime
operations have primitive authority-changing rules. Folding only packages
authority already owned; it cannot mint a guard, allocation, or authority.

Physical storage may remain in specialized indexed registries. Those registries
must agree with resource occurrences and must not independently duplicate
authority. Persistent data-structure copies represent alternative proof
states, not two concurrent owners.

Click's existing `core()` is a borrowing-description projection, not an
implementation of the Iris resource-algebra core. Stable `views` retain their
existing meaning: a borrow freezes its covered memory. A shared protocol
description must not be represented by a stable view of changing payload.

## Composable mutex resources

[Mutex operations as resource contracts](mutex-resource-contracts.md)
describes the implemented subset: named lifecycle operations, typed
protected-state transport, and same-thread acquiring and releasing helpers.
General lifecycle-consuming and lifecycle-producing helper contracts, named
storage transfer, and destruction's named state output remain open.

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

## Shared accounting and reclamation (future work)

For the mutex counter, conserved pending and completed units can satisfy
`pending + completed = 2`, with `counter.value == completed` inside the
protected assertion. Each worker's C increment and unit conversion restore
that assertion before unlock. Join returns the worker's contribution;
neither spawning nor joining invents or destroys population units.

Reference counting needs the same conserved accounting with a different
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

## Implemented mutex resources

Acquisition guards live in the ordinary kernel resource context as
`Resource::MutexGuard`: an opaque acquisition identity with one exclusive
owned unit, no view, no count splitting, and no memory authority. Acquiring
creates the atom alongside the protected assertion; unlock consumes the current
acquisition's atom and the restored assertion. The mutex ledger describes
protocol state; its held bit cannot recreate absent ownership. Stale guard
atoms do not authorize a later acquisition, and direct worker transfer rejects
guards as thread-confined.

The surface lowers `owns mutex_guard(mu)` to `ResourceTerm::MutexGuard`, with
explicit pointer state selection. It resolves the current acquisition
identity; folding must separately consume that atom from the available
resources. Guards compose in ordinary exclusive resource bodies and conditional
model arms. Guard-containing definitions and their transitive wrappers are
thread-confined and marked as guard-bearing for contract checks. Preserving
owned instance inputs containing guards freeze mutex transitions for the checked
body; this boundary is carried in C state, substitution, and state equality, so
nested calls cannot erase it.

Preserving helpers can unfold guard instances using a symbolic acquisition
associated with the mutex pointer, restricted to abstract entries without a
concrete mutex ledger and with every mutex transition frozen. Evaluating a guard
term describes a required resource; only checked unfolding of an owned body
supplies it, and folding consumes it. An exposed guard establishes `held(mu)`;
absence of an exposed guard does not establish `not held(mu)`, and opaque entry
heldness is not interpreted as false. A concrete preserved guard requirement
selects the entry acquisition, even if a later state contains a replacement
acquisition at the same address. Concrete atoms retain their acquisition
address as immutable provenance for source-level missing-resource diagnostics.

Every successful modeled initialization has a fresh internal identity,
independent of the mutex address and protected resource. Lock/unlock retain it;
destroy/init replaces it. Concrete release witnesses must match both the
initialization and acquisition. Loop joins compare initialization identity for
the changed mutexes, so depositing the same protected instance at the same
address cannot disguise a replacement. Replacing a loop-head initialization is
reported as an unsupported contract; a mutex created and destroyed entirely
within an iteration leaves no loop-head obligation.

The lifecycle owner is `Resource::MutexLive` in the same resource context.
Initialization mints exactly one owned atom for its identity; destruction
consumes it. Folded owners cannot authorize either transition until unfolded.
The exclusive resource algebra refuses duplicates, views, and counts; the owner
implies neither memory authority nor heldness, and its identity cannot be
renamed through concrete pointer substitution. Missing ownership reports
`Requires owns mutex_live(...)`.

Heap retirement checks an index of initialized mutex footprints with the
complete ABI storage extent, retained through lock/unlock and removed on
destruction. Direct `free`/`realloc` and allocation retirement at verified calls
use the same check. Lookup visits the affected block and indexed provenance
classes that might alias it; absence from the same-block index is not
separation, so ambiguous overlaps require checked `separate(...)` facts.
Automatic-storage expiry checks the same dependency by whole object at every
scope-leaving outcome and the retained `AutomaticLifetimeEnd` event, and
re-executing a declaration checks the old object first. Symbolic
initializations that might alias a local are refused conservatively.

Initialization checks the full writable storage footprint and ABI alignment
before minting lifetime authority or moving a protected invariant. Ordinary
memory ownership authorizes external storage; live automatic objects supply
implicit storage ownership. Stable views do not authorize it, and active storage
loans block it. The transition forgets the previous byte values of the
footprint. Initialization consumes the explicit ownership of its footprint and
destruction returns it; automatic footprints are instead reserved against
ordinary writes and overlapping initializations until destroy. Independent
abstract inputs carry indexed reservation dependencies derived from their owned
resource definitions; the dependency grants no lifecycle or guard authority.

Use loans, preserving `mutex_use` contracts, named binders, and their remaining
gaps are described in
[concurrency contracts](concurrency-contracts-and-diagnostics.md) and
[mutex resource contracts](mutex-resource-contracts.md).

## Acceptance

Each change needs focused positive and hostile tests and the full
`scripts/check.sh` gate. Changed representations need deterministic multi-size
work regressions. Checking one selected guard or protocol must touch its indexed
support and explicit delta, not scan unrelated protocols, threads, or history.
Verification, expansion/reverification, profiling, and audit must agree.
