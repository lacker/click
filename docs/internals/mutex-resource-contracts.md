# Mutex operations as resource contracts

This design describes mutex operations as ordinary Click resource contracts:
initialization, locking, unlocking, and destruction.

Status: named lifecycle operations, typed protected-state transport, and
same-thread acquiring/releasing helpers are implemented for the subset below.
Named storage transfer and destruction's named state output remain proposals.
`issues/concurrency-and-atomics.md` records the remaining concurrency work.

Mutexes should behave like resources described by ordinary Click contracts.
Their runtime implementation needs trusted rules, but their proof inputs and
outputs should not need a separate naming convention or special `step` syntax.
This document specifies initialization, acquisition, release, and destruction
together so that one operation's outputs fit the next operation's inputs.

This refines [Concurrency contracts and failure explanations](concurrency-contracts-and-diagnostics.md).
For the public contract design, it supersedes the hard-coded initialization
binder `invariant` and the tentative lock output names `invariant` and
`protected`.

## Ordinary contracts determine the proof interface

`pthread_mutex_lock` is a pthread library function, not a C language builtin.
Click's selected runtime gives it a trusted specification. That specification
should expose a contract with ordinary named resource binders, just as a
user-defined function's sidecar does.

In an ordinary contract, `produces item: R` lets a caller write
`let { item: x } = step(...)`. The name `item` belongs to the contract; `x` is
chosen by the caller. The produced resource is independent of the function's C
return value. A mutex operation should follow exactly that rule: `step` must
not invent an output because it recognizes a word such as `protected`.

The standard runtime contracts choose the names below. User-defined contracts
may choose different binder names for the same resource types.

| Contract binder | Resource | Meaning |
| --- | --- | --- |
| `lifetime` | `mutex_live(mu)` | Exclusive lifecycle authority for one initialization, including responsibility for destruction. |
| `access` | `mutex_use(mu)` | Permission to use that initialization while its lifetime is guaranteed. |
| `guard` | `mutex_guard(mu)` | Ownership of one particular acquisition. |
| `state` | The user-defined protected resource | Ownership of the protected data and its currently observed values. |
| `storage` | Existing exclusive memory authority for the mutex representation | Storage consumed by initialization and recovered by destruction. |

The last row names an ordinary memory input/output, not a proposed
`mutex_storage` resource. Its exact range syntax and support for naming raw
memory authority must follow the general memory-resource interface.

An *invariant* is the assertion that must hold whenever the mutex is unlocked.
A `state` instance owns resources satisfying that assertion. Locking returns
ownership of such an instance; it does not return an assertion as a value.
The invariant is not a C argument, a mutable field snapshot, or a new kind of
ownership clause.

## The invariant association

Write `P` in the sketches below for a resource assertion such as
`counter_state(counter)`: the resource family and its parameters, without an
instance binder or observed field values. `P` is explanatory notation, not an
accepted Click type parameter or a new resource named `P`.

Initialization binds one `P` to one fresh mutex initialization. Both lifecycle
authority and borrowed use authority retain that association. A helper checked
independently of its callers must know this association before it can acquire
protected state. A call must check the association against the supplied
initialization; matching the printed mutex address is insufficient.

The revised direction is described in
[Resource arguments and mutex associations](resource-parameters.md). Pass
resources using existing proof arguments and named call maps. Derive the
protected assertion from the checked input authority; do not require a
separate description argument or add angle-bracket resource parameters.

In the sketches below, `P` remains explanatory notation for that recorded
assertion. The unary `mutex_live(mu)` and `mutex_use(mu)` spellings retain the
association internally. An independent helper uses
`mutex_use(mu, counter_state(p))` to identify its protected resource type.
An opaque unary input must not be treated as a known concrete payload.

## The four runtime contracts

These are semantic sketches, not parser-ready declarations. `Storage(mu)`
denotes the existing memory authority for the complete modeled mutex
representation. Its size and alignment come from the selected runtime ABI.
`P` is the assertion associated with the initialization in question. The table
states the full transfer; the subsequent sketches emphasize ordinary contract
clauses.

| Operation | Required inputs | Produced outputs |
| --- | --- | --- |
| Initialize | Consume `storage` and folded `state: P`; require alignment and valid initialization arguments. | `lifetime`; the protected state is placed under the mutex. |
| Lock | Preserve `access` for this initialization. | A new `guard` and freshly observed `state: P`. |
| Unlock | Preserve `access`; consume the matching `guard` and restored folded `state: P`. | No new resource. |
| Destroy | Consume `lifetime`; require every use loan recovered and no outstanding acquisition. | `storage` and folded `state: P`. |

### Initialization

```text
consumes storage: Storage(mu);
consumes state: P;
produces lifetime: mutex_live(mu);
```

The caller must actually own the folded state, with a schema matching its
checked resource declaration. Initialization establishes the association from
that input and the selected mutex, and gives it a fresh initialization identity.
A resource definition or an association alone supplies no ownership. An
ordinary resource needs no mutex-specific member to be associated. Typed use,
acquisition, release, and helper calls retain and check that authenticated
association.

Consuming storage removes ordinary write authority over the initialized mutex
representation. It does not consume ownership of the surrounding allocation
or unrelated fields. The lifecycle resource retains the storage dependency;
it cannot outlive the allocation or local object containing the mutex.

The implementation consumes explicit ownership of the storage bytes at
initialization and returns it at destruction; storage cannot yet be named as a
binder. While the mutex is live nobody owns those bytes, so ownership alone keeps
every write and every transferred footprint off them, in this thread and in
any thread the mutex is shared with. A worker writing protected memory reached
through a pointer into another object therefore needs no separation premise
(`mdtests/mutex_protected_pointer_write.md`), and a contract input's mutex
storage is not checked against the body's writes. Freeing or reallocating the
allocation, and a store or call that needs the bytes, report the live mutex
rather than the missing ownership.

Automatic storage is owned by its scope rather than by a resource, so there
is nothing to consume. Its initialization keeps a write reservation in the
ledger instead, which refuses stores and transferred footprints that may reach
it. No resource can be folded over automatic memory, so a deposited protected
resource cannot carry it either. Allocation-lifetime protection, retirement
refusals, and scope-end checks are unchanged for both kinds.

### Acquisition

```text
owns access: mutex_use(mu);
produces guard: mutex_guard(mu);
produces state: P;
```

The guard records a fresh acquisition of this initialization. The state grants
payload ownership; the guard by itself does not grant access to the payload.
The pair carries a checked association with the same protocol and acquisition.

Observed fields are fresh on each acquisition and constrained by `P`. Earlier
observations remain descriptions of earlier states, not facts about current
memory. Reusing a local name must not reuse an old observation identity.

The use permission survives the call. The guard retains a lifetime dependency
until release, so returning from the lock call or an acquiring helper does not
make the initialization destroyable. This escaping dependency is part of the
contract transfer, not a source-level continuity witness.

### Release

```text
owns access: mutex_use(mu);
consumes guard: mutex_guard(mu);
consumes state: P;
```

Release requires the actual acquisition authority and a restored folded
instance of the associated assertion. Values may have changed while held;
they must satisfy the resource's invariant when returned. A same-address guard
from another acquisition, or a same-family state for different parameters,
cannot substitute. Outstanding payload borrows must end before release.

Folding a wrapper around the guard does not release the mutex. The wrapper
must expose the required authority through ordinary resource operations.
Likewise, renaming a local binder has no effect on acquisition identity.

### Destruction

```text
consumes lifetime: mutex_live(mu);
produces storage: Storage(mu);
produces state: P;
```

Lifecycle authority is exclusive. All loans and guard holds must be discharged
before it can be consumed. Destruction returns the protected resource and raw
mutex storage; freeing the allocation is a separate operation.

If the mutex has been shared, destruction cannot revive the values originally
supplied at initialization. Its returned state is constrained by the invariant
and any separately established guarantees, not by stale observations.
Reinitializing the same address creates a different initialization.

An empty mutex follows the same protocol with the empty protected assertion.
There is no payload ownership to expose. The exact surface treatment of the
trivial `state` binder must be specified together with ordinary empty-resource
contracts; it should not introduce another mutex-specific output convention.

## Call syntax follows from those contracts

With an available named use instance `u`, ordinary named input and output
transport gives the following proposed proof steps:

```text
let { guard: g, state: s } =
    step(pthread_mutex_lock(mu), { access: u });

// Unfold s, verify the C operations, and restore the folded state.

step(pthread_mutex_unlock(mu), {
    access: u,
    guard: g,
    state: s
});
```

The input map names resources already owned; the output pattern introduces
new instances. `guard` and `state` are declared contract outputs, not reserved
keys understood only by the mutex dispatcher. The C call still returns its
ordinary status code. Its proof resources do not become additional C results.

Once ordinary storage binders are supported, initialization and destruction
would have the corresponding shape:

```text
let { lifetime: life } = step(pthread_mutex_init(mu, 0), {
    storage: bytes,
    state: initial
});

// Checked borrowing of life supplies use authority for calls.

let { storage: bytes_after, state: final } =
    step(pthread_mutex_destroy(mu), { lifetime: life });
```

These examples do not establish new syntax for introducing `u` or `bytes`.
Those introductions need general loan and memory binding rules. The existing
checked conversion from lifecycle authority to a synchronous use loan should
remain available, but its interaction with explicit named input maps must be
specified. It must select supplied authority rather than search for a
convenient matching instance, and an escaping guard must retain the loan.

The former initialization spelling
`step(pthread_mutex_init(mu, 0), { invariant: initial })` was a hard-coded
selection hook. It has been replaced by schema-declared state input and lifetime
output transport. The complete storage transfer and protected-state association
remain pending; renaming the key alone would not complete the migration.

## Preserving, replacing, and packaging resources

An ordinary helper with `owns guard: mutex_guard(mu)` preserves that acquisition.
Unlocking and relocking cannot satisfy that promise. A helper that replaces an
acquisition must consume an input guard and produce a new output guard, just
as it would replace any other resource occurrence.

User-defined wrappers may package a guard and protected state together. They
may also package lifecycle or use authority subject to the ordinary lifetime
rules. Folding a wrapper changes the presentation of owned resources; it does
not initialize a mutex, acquire it, grant access, or discharge a loan.

The selected runtime supplies the default contracts. User-defined helpers can
use the same clauses and binding machinery. Trusted code remains responsible
for the actual mutex transition, fresh identities, interference, and storage
effects; it must not bypass ordinary resource input/output validation.

The current modeled runtime assumes successful valid operations under its
checked preconditions. These sketches do not prove the operating system's
implementation, absence of deadlock, or termination. A runtime profile that
models failure or a future try-lock operation needs outcome-dependent resource
contracts: failure cannot produce a successful acquisition's guard or state.
The status result and resource outputs must describe the same outcome.

## Failures should name the missing requirement

Missing authority should use existing Click resource terms:

```text
Requires owns mutex_use(mu)
Requires owns mutex_guard(mu)
Requires owns counter_state(counter)
Requires owns mutex_live(mu)
```

An association mismatch should identify the supplied authority and its
protected resource, alongside the required resource such as
`counter_state(counter)`. Matching by address must not suppress this failure,
and a separate description argument must not be offered as a repair.

Where a supplied occurrence is incompatible, identify it and its source: the
required entry guard versus the newly acquired guard, or the lifetime whose
loan remains outstanding. Do not invent a `not_held` fact just to phrase a
protocol failure as a missing proposition. Report the outstanding resource or
loan and its source location. Distinguish an unsupported contract form from
missing ownership.

The checker may track generations, receipts, and loan identities internally.
Ordinary diagnostics should name the relevant Click resources and binders,
not expose those implementation structures.

## Current boundary and implementation sequence

The runtime now declares one shared binder schema for all four operations.
Implemented projections pass through the ordinary parser's supplied/produced
binder checks. Initialization's named form is:

```text
let { lifetime: life } = step(pthread_mutex_init(mu, 0), { state: initial });
step(pthread_mutex_destroy(mu), { lifetime: life });
```

For an empty mutex, initialization has no state input:

<!-- verified-example: mdtests/mutex_helper_transfers_unary.md -->
```click
let { lifetime: lifetime } = step(pthread_mutex_init(&p->mu, 0), {});
```

An omitted state input initializes an empty mutex; it does not infer or deposit
an owned resource from any declaration.

The kernel independently checks those maps and binds the output to the actual
owned initialization. Named preserving `owns life: mutex_live(mu)` and
`owns g: mutex_guard(mu)` helpers are implemented. Names select exact authority;
they have no fields or body to unfold. Checked preserving calls reconnect each
name only to the same returned authority. Old lifecycle names fail after
destruction and reinitialization at the same address.

Direct unary preserving `mutex_use` contracts support balanced opaque
lock/unlock, exposing no protected state. Named use inputs are supported:
`owns access: mutex_use(mu)` accepts an explicit named use or lifecycle authority.
The call borrows the selected authority, binds a scoped callee use permission,
and restores the caller's original authority and name after checked recovery.
Nested reborrows select the same exact source; matching only the mutex address
cannot substitute a sibling permission.

Typed permissions also identify the protected resource with
`mutex_use(mu, counter_state(p))`. Their runtime acquisition returns a fresh
state, and release accepts a restored replacement instance of that same type.

Unlocking forgets the memory the released instance owns, so that a thread
caches nothing about protected memory while it does not hold it. The
footprint is derived at release, while the thread still owns the instance and
its memory names the footprint exactly; a footprint the derivation cannot name
forgets every cell the thread does not keep owning. Acquisition then changes
no memory: it mints the fresh instance, and its unfolding names the protected
memory again. The protected resource may own named children, and its
footprint may depend on memory, such as a vector reached through a pointer
cell. Field schemas must not be matched, conditional, recursive or
witness-bearing. `mdtests/mutex_protected_named_child.md` acquires a named
child, and `mdtests/mutex_protected_pointer_footprint_stale_read_rejected.md`
refuses a value read through a pointer in an earlier critical section.

### Acquiring and releasing helpers

A verified helper can expose those transfers in an ordinary contract:

<!-- verified-example: mdtests/mutex_helper_transfers.md -->
```click
void acquire(struct counter *p) {
    owns access: mutex_use(&p->mu, counter_state(p));
    produces guard: mutex_guard(&p->mu);
    produces state: counter_state(p);
}

void release(struct counter *p) {
    owns access: mutex_use(&p->mu, counter_state(p));
    consumes guard: mutex_guard(&p->mu);
    consumes state: counter_state(p);
}
```

The `mdtests/mutex_helper_transfers.md` executable example includes their
proofs, nested wrappers, and callers. It uses ordinary named call maps:

<!-- verified-example: mdtests/mutex_helper_transfers.md -->
```click
let { guard: acquired, state: contents } = step(acquire(p), { access: access });
step(release(p), { access: access, guard: acquired, state: contents });
```

The output names belong to each contract. A wrapper may rename them, and its
proof may name the actual acquisition differently from its declared output.
Neither renaming nor a `produces` clause creates authority. The acquiring body
must establish the real acquisition and the owned protected state. The
releasing body must discharge the acquisition's lifetime hold by unlocking;
dropping its visible guard resource does not establish `consumes`.

Independent helper entry ties permission to one rooted input use authority.
Return checks tie the exported guard to that exact root and initialization.
A caller summary applies the checked acquire/release exchange in the caller's
scope, preserving its original use or lifecycle source. This keeps an exported
guard's lifetime dependency alive across nested synchronous calls. A preserving
`owns guard` contract still returns the exact entry acquisition; unlock followed
by relock cannot satisfy that promise.

The initial helper subset has one directly named preserved use input, one
produced or consumed guard, and, for typed use, one matching protected-state
transfer. Viewed or conditional resource clauses and additional mutex protocol
transfers are outside this subset. Empty-mutex helpers can use unary
`mutex_use(mu)` without a state clause; they cannot stand in for a typed
transfer that must restore exposed protected state. Helper transfers accept
only unconditional leaf resources with fixed memory footprints; runtime typed
use also accepts named children and memory-dependent footprints. These
transfers are synchronous and stay on the same thread. They do not permit moving pthread guard ownership to a worker.

A worker created with `pthread_create` under `runtime "modeled-pthread"`
receives its preserved `mutex_use` the same way, as a loan split from the
parent's `mutex_live` or retained use share, so the parent keeps a retained
share and may lock while the worker is pending. `pthread_join` returns only
that loan: it ends the worker's scope, rejoins the shares, and restores the
parent's source, `mutex_live` once the last worker has joined. The worker's
preserved use fact is a loan of that source and is not composed into the
parent's frame, so after join the parent holds exactly what it held before
the create, and a plain lock, a further create, or destroy proceeds with no
use fact left behind. `mdtests/modeled_pthread_lock_after_join.md` is the
regression.

A releasing helper can modify the payload and deposit a replacement instance.
Its summary must forget earlier field and memory observations consistently
with that mutation. Acquiring again does not recover an old value merely
because the proof reuses a resource type or name.

### Remaining boundary

General lifecycle-consuming/producing helper contracts, named storage, and
named destruction outputs remain unfinished. The four runtime sketches above
include those future projections; the implemented acquire/release subset does
not imply all four operations have a fully ordinary source-level contract.
Direct `pthread_mutex_t *` parameters also remain unsupported by the sidecar
parser; the frozen `mdtests/mutex_helper_transfers_empty.md` regression
records that limitation without rewriting its C.

The acceptance boundary includes independently checked bodies and call
certificates, missing lock/unlock rejection, stale acquisition and observation
rejection, and refusal to destroy while acquisitions or use loans survive.
Preserve existing C as the regression boundary. Do not rewrite C into a more
convenient proof shape.

Exact shared-counter accounting, richer protected-resource composition, and
atomic publication remain separate work in the concurrency roadmap.

## Ordinary memory helpers under a held lock

A synchronous helper may receive memory exposed by unfolding the protected
state, using an ordinary `owns` or `views` contract. It need not receive the
mutex guard when it does not perform a mutex operation. Argument binding and
summary recovery preserve the caller's protocol ledgers, including folded
guards and opaque acquisition receipts. A live mutex's storage is owned by no
one, and automatic storage stays reserved, so absence of a protocol clause does
not authorize reinitialization or raw writes to a live mutex.

The worker admission restriction remains separate: this change does not relax
suspended-worker protocol transfer or stateful population confinement.
`mdtests/mutex_population_body_helper.md` and
`mdtests/mutex_guard_frames_ordinary_call.md` exercise ordinary helper framing.


## Authority-bearing controls

A mutex protecting a population protects an ordinary control that owns the
population's authority; no mutex rule refers to populations. The control
declares a
proof field so that it is a named instance, which the initialization `state`
binder requires:

<!-- verified-example: mdtests/authority_mutex_control_deposit.md -->
```click
resource control(obj: struct object*) {
    field refs: int32;
    owns obj->refs;
    owns authority(reference(obj));
    fact obj->refs == refs;
    fact refs == count(reference(obj));
}
```

The creator establishes the authority, folds the control, and deposits it at
initialization. Locking returns the same control with the acquisition guard.
Inside the critical section the returned authority permits member changes and
count observations. Unlocking requires the control folded again under the
deposited binder, with its facts true at the current population total.
Destruction returns the control.

While the control is in the mutex, its authority is in no thread's resource
context. A member held outside the mutex therefore grants no count
observation, and no thread can change the population. Locking a different
mutex returns no control, and an earlier initialization's lifetime cannot
destroy a later one. The same control also works sequentially with no mutex.

The regressions are `authority_mutex_control_deposit.md`,
`authority_mutex_control_sequential.md`,
`authority_mutex_control_unlock_open_rejected.md`,
`authority_mutex_control_bad_increment_rejected.md`,
`authority_mutex_member_alone_rejected.md`,
`authority_mutex_control_wrong_mutex_rejected.md`,
`authority_mutex_control_stale_initialization_rejected.md`, and
`authority_control_instance_duplicate_authority_rejected.md`.

The acquiring and releasing helpers described earlier on this page also carry
an authority-bearing control. Click admits exactly that contract shape: one preserved typed `mutex_use`, one produced or consumed guard, and
the matching protected state, with no other clause. The caller applies the
checked runtime exchange, so the control moves between the mutex and the
caller without any population change. Each acquisition returns a fresh
instance whose fields are unknown. The control's facts tie it to the current
population total, so a count observed before an earlier critical section
remains historical. The regressions are `authority_mutex_control_helpers.md`,
`authority_mutex_control_helper_stale_count_rejected.md`,
`authority_mutex_control_helper_missing_state_rejected.md`, and
`authority_mutex_control_helper_wrong_mutex_rejected.md`.

A helper's own proof may also open the control it acquires. The typed lock
enters the control's population into that proof with a fresh total, bounded
below only by the members the helper already owns and carrying no creator
right. A proof enters each population at most once, so a second acquisition
in the same helper is refused rather than allowed to reuse the first total.
Under that authority the helper may observe the total and fold or unfold
members. Its contract keeps one preserved typed `mutex_use` and declares at
most one member effect, a `consumes` or `produces` of one member of the
acquired population. At return, the checked births and deaths under the
acquired authority must equal that declaration exactly: an undeclared change,
a declared death that was not spent, and a member of a population the helper
never acquired are each refused. Births and deaths are the only events that
change the recorded total, and both need the authority, so the change stays
authentic after unlock returns the authority to the mutex. The caller applies
the declared member effect to the population held by the mutex. The
regressions are `authority_mutex_control_helper_open.md`,
`authority_mutex_locked_release.md`,
`authority_mutex_locked_release_unspent_rejected.md`,
`authority_mutex_locked_release_other_population_rejected.md`,
`authority_mutex_locked_release_stale_rejected.md`,
`authority_mutex_locked_undeclared_birth_rejected.md`, and
`authority_mutex_locked_reacquire_rejected.md`.

A locked helper may also run as a `pthread_create` worker, and several may be
outstanding at once. Create lends no authority; each worker's declared change
applies at its join, and the parent cannot count the population until then
(the [worker authority protocol](worker-authority-protocol.md#workers-that-lock-the-populations-control)).
The regressions are `authority_mutex_locked_workers.md`,
`authority_mutex_locked_workers_reverse_join.md`,
`authority_mutex_locked_workers_parent_lock.md`,
`authority_mutex_locked_workers_pending_count_rejected.md`,
`authority_mutex_locked_workers_stale_rejected.md`, and
`authority_mutex_locked_workers_destroy_before_join_rejected.md`.

A locked helper may declare one member effect per population whose control it
acquires, such as a retain that consumes a `permit(obj)` and produces a
`reference(obj)`. A proof that holds only a typed `mutex_use` share may call a
locked helper: the call enters the escrowed populations into that proof with
fresh totals, as a lock would, and the proof's exit check compares its own
declared change with what the calls changed. `examples/shared-refcount` uses
both, with a stated cap on references that bounds the retain's increment.
