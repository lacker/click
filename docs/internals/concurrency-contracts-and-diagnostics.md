# Concurrency contracts and failure explanations

This design proposes the contracts a reviewer reads for concurrent C code and
how Click explains each unproved concurrency requirement.

Status: evolving design; implemented surface forms and remaining proposals are marked below.

The human review boundary is the C source, its contract, and an explanation of
each unproved requirement. A reviewer should not need to understand the mutex
ledger, certificate representation, or tactic dispatcher to judge those things.
This document puts that boundary before the implementation plan.

It refines the [resource-invariant design](resource-invariants.md)
and the [shared-counter protocol](https://github.com/clicklang/click/blob/master/design/concurrency-probes/mutex-shared-protocol.md). Existing failure
classification is described in [proof-failure triage](../concepts/proof-failure-triage.md).

The uniform target interfaces for initialization, lock, unlock, and destruction
are specified together in [Mutex operations as resource contracts](mutex-resource-contracts.md).
Its named lifecycle checkpoint replaces the special initialization binder with
declared state input and lifetime output transport; the complete interface is
still being implemented.

## What exists and what would change

Today, `owns mutex_guard(mu)` can occur directly in preserving function
contracts and in declared resource bodies. `owns h: holding(counter)` can
preserve a folded guard wrapper through a helper. The
helper can unfold and refold the wrapper, establish `held(mu)` from the exposed
guard, and use separately supplied protected memory. It cannot change mutex
protocols. This is a conservative implementation
boundary, not the proposed final meaning of concurrency contracts.

Modeled initialization also has a generative internal identity. Loop joins
preserve it, distinguishing balanced lock/unlock from destroy/init at the same
address, even when the protected assertion is identical. Replacing a loop-head
initialization is currently refused with an explicit unsupported-contract
message. A mutex may still be initialized and destroyed entirely within an
iteration. The lifecycle resource described below now carries that identity;
the complete storage-lifetime and `mutex_use` protocol remains future work.

Heap allocation retirement now checks initialized mutex storage. The modeled
ABI records a 40-byte mutex footprint, indexed by memory block. Direct `free`,
`realloc`, and helper contracts that retire or may replace an allocation refuse
an overlapping initialized mutex. Retirement also checks indexed provenance
classes for possible aliases, including symbolic addresses that may designate
an allocation with a different block identity. Unresolved overlap reports the
required `separate(...)` fact. Destruction removes this dependency; unlocking
does not. Abstract preserving contracts now derive reservation dependencies
from their owned inputs and require separation before allocation retirement.
This retirement check adds no surface syntax. Initialization storage checks
and write reservations are described below; synchronous use loans are implemented.
Automatic-storage expiry is now checked as described below.

The first lifecycle ownership layer now implements `owns mutex_live(mu)` in
preserving contracts and declared resource bodies. Initialization creates one
exclusive resource for its generation. Locking requires that resource to be
available; destruction consumes it. Folding hides authority from both operations
until unfolding restores it. An address, an initialized ledger entry, or an old
generation's resource cannot substitute for the owner. Missing ownership reports
`Requires owns mutex_live(mu)`. This resource supplies neither `held(mu)` nor
memory access. It cannot be viewed, counted, or transferred to workers yet.

Synchronous preserving `owns mutex_use(mu)` contracts now borrow lifecycle
ownership or reborrow use authority. Such helpers may now perform balanced
opaque lock/unlock, granting no protected payload. Guard outputs and worker
transport remain pending.
Preserving lifecycle contracts
retain the same conservative transition freeze as preserving guard contracts;
`consumes`/`produces` and named primitive lifecycle binders remain unsupported.

Automatic storage now cannot end while it contains an initialized mutex.
The check covers normal block exit, `break`, `continue`, `goto`, return, and
exceptional outcomes, including the retained certificate for scope retirement.
Re-executing a declaration checks the old object's mutex dependencies before
replacing its storage, for scalar declarations and aggregate construction alike.
It consults the initialization index, so folding `mutex_live` or a guard cannot
hide the dependency. Destroying all mutexes in the object permits its lifetime
to end; unrelated concrete objects can end independently. A symbolic mutex
pointer that might designate local storage is refused conservatively with an
explicit limitation diagnostic. No new surface syntax is needed.

C fixtures cover return, loop exits, folded ownership, and loop reentry. The
small C frontend still rejects standalone compound statements; unchanged
nested-block fixtures record that limitation rather than presenting a rewritten
C program as coverage. Kernel tests exercise all scope-leaving outcomes.
Uninitialized stack structs now need only their storage layout, so containing
an opaque pthread union does not require typed-copy support; unsupported
aggregate copies remain rejected.

Initialization now requires the full mutex storage and its ABI alignment.
For an external struct parameter, the contract can say:

<!-- verified-example: mdtests/modeled_pthread_empty_mutex.md -->
```click
owns holder->mu;
requires aligned(&holder->mu, 8);
```

`owns holder->mu` now supports an opaque union field as byte storage; this is
an extension of an existing resource spelling, not a new resource kind. Its
extent comes from the C layout, including the field's storage padding, so the
contract does not hard-code the 40-byte size. It does not provide typed union
copying. `views` never supplies initialization ownership. A local automatic
object has implicit storage ownership; a sufficiently large allocation supplies
ordinary memory ownership and allocator alignment. An address alone is not
permission to initialize. Failures name the missing owned range or
`Requires aligned(..., 8)`.

Initialization checks known read-only and ended storage and active stable loans
before moving an invariant or creating `mutex_live`. It forgets old byte values
in the initialized footprint; adjacent cells remain available. Constant owned
spans are indexed in byte units, so unrelated fields of the same object do not
make each initialization scan the whole resource context. Nonconstant bounds
can be proved for a single owned span at the selected base; this checker does
not search an ambiguous symbolic partition or implicitly join separate ranges.

Successful initialization now reserves that footprint until destruction.
Ordinary stores, aggregate writes, call-result assignments, and overlapping
initializations require separation from every possibly affected reservation.
A preserving helper's mutable contract footprint is checked at application too,
so a modular call cannot bypass the restriction. Adjacent payload remains writable;
unlocking, hiding the owner inside a resource, or removing its visible atom does
not release the reservation. Failure reports `Requires separate(...)` using the
attempted write and reserved byte ranges. No new surface predicate is added.

The reservation index selects overlapping concrete byte intervals, including
multiple mutexes inside one object. Ambiguous symbolic footprints require
separation evidence. Checked runtime mutex calls bypass the ordinary-write gate
but still respect stable storage loans and forget old representation values.

Independent preserving contracts now derive the same storage dependencies from
owned `mutex_live` and `mutex_guard` inputs, including folded resources, named
children, and matched bodies. The derivation uses the existing resource-definition
footprint traversal once at entry. The resulting indexed reservation stays with
the checked C state across assignments, folding, calls, and loop joins; it does
not grant a live owner, a guard, or permission to change the protocol.

An undecided match reserves the union of its possible mutex footprints. Recursive
or unresolved descriptions conservatively reserve an unnamed footprint, so
external writes remain blocked when Click cannot name the storage dependency.
Fresh automatic objects are independent of these pre-existing inputs. Known
footprints permit adjacent payload writes and separated allocation retirement;
missing evidence reports `Requires separate(...)`. No surface syntax is added.

Preserving contracts still freeze mutex protocol transitions. Lifecycle outputs
remain future work; preserving `mutex_use` lending is implemented.

The surface status is:

| Surface | Status in this proposal | What a reader should understand |
| --- | --- | --- |
| `pthread_mutex_init(mu, 0)` with `{ state: s }` | Implemented | Initialization makes `s`'s resource assertion the one this mutex protects. |
| `owns mutex_guard(mu)` in a resource body | Keep the existing spelling | This resource contains ownership of a current acquisition, not merely knowledge that the mutex is locked. |
| Direct `owns mutex_guard(mu);` clauses | Implemented for preserving helpers | Receives and returns the entry acquisition; all mutex transitions remain prohibited. |
| Direct named guard clauses, such as `owns g: mutex_guard(mu);` | Implemented for preserving helpers | The function receives and returns the same guard occurrence. |
| `consumes` and `produces` for guards | Extend existing clause semantics; not supported today | The function can surrender an acquisition or return a newly established one. |
| `mutex_live(mu)` | Implemented for direct preserving `owns` clauses and resource bodies | Lifecycle ownership of this initialized mutex, including responsibility for destruction. |
| `mutex_use(mu)` | Implemented for direct synchronous preserving `owns` clauses | Permission to use this initialization while its lifetime is guaranteed. It gives no payload access. |
| Acquisition numbers, protocol generations, ledger annotations | Keep internal | Source contracts should not need to name checker bookkeeping. |
| A new `uses` clause or general effect language | Do not add initially | Use ordinary `owns`, `views`, `consumes`, and `produces` clauses; preserve their distinctions. |

The examples below are proposed contract sketches. They are not passing Click
fixtures or promises that the current parser accepts every spelling. In
particular, consuming/producing primitive clauses and protected-state outputs
still need the transfer rules described below. Preserving named primitive
binders are implemented as summarized at the end of this document.

No C implementation changes are required by this proposal.

## Contracts a reviewer would read

### A helper that uses already-protected memory

```text
int32 read_locked(struct counter *counter) {
    owns g: mutex_guard(&counter->mutex);
    owns s: counter_state(counter);
    ensures result == s.value;
}
```

Reading this contract: the caller supplies the acquisition and the protected
state. The function returns the guard and state and returns the stated value.
The guard alone does not give access to `counter->value`. The memory authority
comes from `counter_state`, whose definition is visible to the reviewer.

The direct guard binder preserves its acquisition identity. It cannot be
discharged by an unlock followed by another lock, even if the address is equal.

An ordinary declared wrapper can contain the guard and protected state so a
larger API does not repeat these ingredients at every call. Folding that wrapper
packages authority already owned; it does not create a lock acquisition.

### A helper that acquires

```text
void acquire_counter(struct counter *counter) {
    owns u: mutex_use(&counter->mutex);
    produces g: mutex_guard(&counter->mutex);
    produces s: counter_state(counter);
}
```

Reading this contract: the mutex must stay alive. On successful completion the
caller obtains an acquisition and current protected state. The use permission
is returned and must remain live while the guard is held. This contract does
not promise that `s.value` equals a value observed before the call, nor that the
call terminates. These examples use the current modeled runtime's successful
valid-lock assumption; a failure-returning profile needs separate outcomes.

The checker must connect `g`, `s`, and `u` to the same initialized protocol.
Matching their printed addresses is not sufficient evidence of that connection.

### A helper that releases

```text
void release_counter(struct counter *counter) {
    owns u: mutex_use(&counter->mutex);
    consumes g: mutex_guard(&counter->mutex);
    consumes s: counter_state(counter);
}
```

Reading this contract: release gives up this acquisition and returns the restored
protected assertion to the mutex. The caller may still use the live mutex, but
cannot continue accessing its payload through `s`. Outstanding borrows of that
payload must end before release.

A helper that releases and reacquires must describe an input guard being consumed
and an output guard being produced. Equal mutex addresses do not make the two
acquisitions interchangeable.

### Lifecycle ownership and borrowed use

Initialization requires exclusive live storage for the C mutex and the protected
assertion. It establishes `mutex_live(mu)` and places the assertion behind the
lock. The initialized mutex owns/reserves its storage for runtime use; this does
not authorize ordinary C writes to its representation.

A call requiring `mutex_use(mu)` may receive a checked loan from an available
`mutex_live(mu)` owner, or a checked reborrow from an existing use permission.
Each loan has its own authority identity. Several workers can have distinct
loans; no worker receives a duplicate owner or a copy of the protected assertion.
An ordinary synchronous call returns the loan at its boundary when no returned
resource still depends on it. A returned guard retains the lifetime dependency
until release: merely returning from `acquire_counter` cannot make the mutex
destroyable again. The caller must retain the supplying owner or use permission;
a guard cannot escape that lifetime. A worker's loan lasts until its matching
join, including while it waits to acquire the mutex. Create failure recovers
only the loan that was not transferred to a child.

Destruction requires lifecycle ownership with every use loan recovered and no
outstanding acquisition. It returns the protected assertion and ends this mutex
initialization. Freeing the storage is a separate operation.

This is a proposed extension of checked borrowing, not a reinterpretation of
`views` over changing memory. A use permission preserves identity and lifetime;
it does not freeze mutex state or protected payload. The owner cannot bypass a
loan by destroying, reinitializing, or freeing through another pointer alias.

Both new capabilities should be usable inside declared resources. Initially,
use permissions should be returned or reborrowed, not independently retained
beyond their lender's lifetime. More general reference-counted lifetimes can be
added through a separate resource protocol; they are not necessary for joined
workers.

## Recommendation: no separate continuity witness

Use existing resource preservation and replacement clauses to express acquisition
continuity. Do not add a `continuous` clause, epoch-valued field, or a second
resource whose only purpose is to certify that the guard stayed held.

```text
owns g: mutex_guard(mu);       // Return this guard.
```

For a helper that may release and reacquire:

```text
consumes g: mutex_guard(mu);   // The input guard need not be returned.
produces next: mutex_guard(mu);
```

These are different contracts. In the first, `g` denotes the input resource
occurrence, not an existential slot that any guard at the same address can fill.
The binder gives that occurrence a readable name; it does not strengthen the
meaning of an otherwise anonymous preserved primitive guard clause. Release
consumes the input occurrence, and reacquisition supplies a different one. The
second contract permits replacement; it does not by itself prove that release
and reacquisition occurred. The body must justify the output resource.

The kernel keeps acquisition identities internal. A diagnostic can distinguish
`g` from `next` using source binders and their introduction/consumption sites,
without requiring the user to compare acquisition numbers.

A declared wrapper is different. `owns h: holding(counter)` returns that declared
resource according to its definition and contract. Its existential ingredients
may have been reconstructed. Do not infer uninterrupted holding merely because
the wrapper's identity or visible model is unchanged, and do not silently freeze
its model fields to obtain that stronger meaning.

When a client specifically needs the same acquisition preserved across a helper,
expose the guard as an ordinary contract resource. A caller can unfold its
wrapper, pass the guard and any required body resources, and refold afterwards.
It cannot pass both the folded wrapper and the guard contained in it as two
independent owners. If the wrapper intentionally hides its guard, its public
contract must be useful without promising the hidden guard's identity.

This leaves wrapper abstraction intact and puts the stronger requirement in a
contract the human can read. No separate continuity witness is needed for the
initial design. Revisit that decision only for a concrete API whose necessary
contract cannot be expressed this way; do not preemptively add a new surface
concept.

The implemented opaque checkpoint is safe because it forbids every mutex
transition. Removing that prohibition must implement the rules above, including
snapshot/authority checks: a replacement guard cannot revive observations about
current memory from an earlier acquisition. A value can still be proved equal
across acquisitions when the invariant or another checked argument establishes
that equality; continuity is not the only possible proof.

## Loop contracts use existence, not fixed acquisition numbers

For the unchanged [parity program](https://github.com/clicklang/click/blob/master/design/concurrency-probes/mutex_held_parity.c), the intended loop meaning
is: an even index owns no acquisition; an odd index owns some current acquisition
of this initialized mutex. The model can express `Idle` and `Holding` with the
guard as a resource ingredient in the `Holding` arm.

The loop opens that assertion at its head and must rebuild it at each backedge.
It may supply a fresh acquisition as the next iteration's witness. Reusing the
assertion does not require reusing the previous witness and cannot create a
missing guard. Branches must prove their relation to the model/index.

"This thread has no guard" is not "the mutex is globally unlocked." Another
thread may hold it. A lock operation requires live-use permission, not a proof
that no other thread currently holds the lock.

### Implemented parity checkpoint

The [unchanged parity sidecar](https://github.com/clicklang/click/blob/master/design/concurrency-probes/mutex_held_parity.click)
uses an ordinary scalar field and conditional `owns mutex_guard(...)` body.
At a loop head, the kernel records symbolic heldness and a fresh acquisition
description only after checking the declared wrapper against real entry
custody. The description supplies no owned guard. Unfolding the checked
wrapper is still necessary to obtain ownership for unlock. At each backedge,
the returned wrapper must account for actual heldness before its model fields
are abstracted; other mutex protocols retain their exact comparison.

This checkpoint requires an empty mutex, owned lifetime, and a direct
conditional guard body. It does not abstract protected payloads, use holds,
or joins between different exit receipts. The proof covers all signed input
values, using a separate proof case for the skipped negative-input loop.
Checked remainder arithmetic establishes parity after increment without
changing the C source or treating a bounded unrolling as an induction proof.

The direct loop clause `if i % 2 == 1 { owns mutex_guard(&object->mutex); }`
also verifies the frozen source. Its private ordinary resource captures the
head condition as a scalar field; a pointer-indexed lookup locates the owned
instance for checked unfolding at a mutex operation. The lookup supplies no
ownership. At each backedge, checked folding establishes the newly evaluated
condition before the models are normalized for comparison. Changing the index
without performing the required mutex transition therefore fails, even when
the mutex ledger itself has not changed.

This form currently accepts scalar comparisons over C values for mutex guards.
Conditions such as `held(mutex)` cannot define their own ownership. Other
conditional loop resource clauses use the ordinary decided-condition rules.
The explicit named-resource form remains available and uses the same guard
ownership checks.

## Failure explanations are part of the design

Every implemented operation must have a corresponding human-facing failure
contract. Designing an acceptance rule without its refusal explanation is
incomplete work.

For an unmet proof requirement, use this information order:

1. The C source location and operation, plus the related contract/loop clause.
2. **Requires:** the exact Click proposition or resource clause, including access
   mode, arguments, binder identity, and relevant snapshot when needed.
3. **Available:** a small relevant selection of facts/resources on this path.
4. **Why it does not suffice:** the specific mismatch, with source provenance.
5. A next investigation or proof step supported by the evidence, if one exists.

The requirement is written in Click terms, not replaced by an English paraphrase.
For a fact, print `Requires counter->value == completed`. For a resource, print
`Requires owns mutex_live(&counter->mutex)` (or the applicable `views` clause).
Ownership and a view must not print as the same obligation. Explanatory prose
follows only when it helps distinguish the required term from the available one.
Automatic lending, reborrowing, and framing may remain sophisticated internally;
their failures must expose the particular resource requirement they could not
satisfy. A checker limitation must be identified separately.

A printed binder such as `g` refers to the existing contract/proof binding, not
an invitation to declare a fresh resource with that name. When two resources
have the same printed arguments, retain the binder and source provenance that
explain why only one can satisfy the obligation. A diagnostic that erases this
distinction is imprecise even if its resource type is correct.

Locations below are placeholders, not claims about current fixture line numbers.
Names must be taken from the user's program and contracts. Internal identities
may be displayed as local explanatory labels such as "the acquisition at line
18" when ambiguity requires them; raw ledger IDs are not the primary message.

### Access without protected ownership

```text
Cannot verify this write at counter.c:<line>:
    counter->value = counter->value + 1;

Requires owns counter->value
Available: owns u: mutex_use(&counter->mutex)
That permission keeps the mutex alive; it does not give access to its payload.
The counter_state resource that owns this field is protected by counter->mutex.
```

Do not say "you forgot to lock" unless the evidence supports that diagnosis.
The code could already have acquired the lock while the proof still holds a
folded resource. In that case, identify that resource and suggest unfolding it
only when its selected body actually supplies the required ownership.

### Unlock with a guard still inside a wrapper

```text
Cannot verify pthread_mutex_unlock(&counter->mutex) at counter.c:<line>.

Requires owns mutex_guard(&counter->mutex)
Available: owns held_state: holding(counter)
The selected Holding arm of held_state contains the required guard.
Unfold held_state before this call.
```

The implemented unlock diagnostic now leads with
`Requires owns mutex_guard(&counter->mutex)` when the acquisition is absent,
already consumed, or still packaged in a resource. It does not yet inspect
wrappers to suggest an unfolding step. If both guard and protected instance
are unavailable, it reports the guard first.

When the guard is available but the protected instance is not folded, the
message instead names the exact resource application, for example
`Requires owns counter_state(counter)`, and identifies it as the instance
selected at `pthread_mutex_init`. It does not print internal instance numbers
or require the instance's historical model-field values. The kernel still
checks the selected instance identity; another instance of the same resource
cannot satisfy the obligation. Source binder names and declaration locations
remain future diagnostic work.

Only make this suggestion when the `Holding` arm is established. Otherwise the
missing requirement is the model/branch fact selecting that arm, not an
unconditional instruction to unfold.

### Missing restored invariant

```text
Cannot return counter_state to counter->mutex at counter.c:<line>.

Requires counter->value == completed
Available: counter->value == previous + 1; completed == previous
This path updates the C counter but has not established the matching
contribution update required by counter_state.
```

These available facts must be actual checked facts, not a guessed explanation.
The report names the invariant clause defining the equality. It does not
automatically recommend weakening that invariant or changing the C program.

### Destruction before a worker's use ends

```text
Cannot verify pthread_mutex_destroy(&counter->mutex) at counter.c:<line>.

Requires owns mutex_live(&counter->mutex)
Unavailable while borrowed: mutex_live(&counter->mutex)
Outstanding use: mutex_use(&counter->mutex), lent to second at pthread_create(...)
This path has joined first, but has not recovered second's use permission.
```

This can indicate a C lifetime bug or missing join/resource-transfer evidence.
Report the distinction as unresolved until the proof establishes which it is.

### An observation from an earlier acquisition

```text
Cannot establish counter->value == saved at counter.c:<line>.

Requires counter->value == saved
Earlier fact: counter->value == saved, at the read before unlock at counter.c:<earlier line>
That fact describes the earlier state, not the current counter->value.
The mutex was released and acquired again; another worker may have changed it.
```

A historical fact remains true about its original read. Do not report that the
fact itself became false or was arbitrarily erased.

### A contract that promises the same guard

```text
Cannot establish the return requirement for g in helper's contract.

Requires owns g: mutex_guard(mu)
Available: owns next: mutex_guard(mu)
g was consumed by pthread_mutex_unlock(mu) at helper.c:<line>.
next was produced by pthread_mutex_lock(mu) at helper.c:<later line>.
```

Whether the contract should describe replacement or the C should avoid releasing
the lock is a human decision. The diagnostic must explain the discrepancy first.

## Do not disguise every failure as a missing fact

The desired `Requires X` explanation applies to semantic proof obligations.
It is misleading for other failures:

| Situation | Required explanation |
| --- | --- |
| Bounded search did not find a proof | Name the remaining goal and relevant premises; say it is not yet proved, not false. |
| Click lacks the needed rule | State the unsupported operation and the valid proof obligation that cannot yet be represented or checked. |
| Verification exceeded a budget | Identify the operation/phase and budget; do not invent a missing program assumption. |
| Internal checker/certificate inconsistency | Identify a Click failure and preserve a reproducible case; do not blame the C program. |
| A counterexample is established | Show the admitted path and violated requirement, distinguishing symbolic evidence from an executed test. |

Preserving helpers now support abstract guard opening. The remaining limitation
on lock-changing helper contracts should eventually be reported along these lines:

```text
Cannot yet verify pthread_mutex_unlock(mu) at helper.c:<line>.
Available: owns g: mutex_guard(mu)
Click does not yet support consuming an acquisition across a helper boundary.
This is a verifier limitation, not a missing contract resource.
```

Printing `Requires false = true` as a substitute for that explanation is unacceptable.
Likewise, "resource transfer failed" or "protocol state mismatch" is useful only
as a secondary implementation label, after the program-level requirement.

Do not claim a necessary resource is absent from the entire state merely because
a tactic did not expose it. Distinguish absent, folded, borrowed away, associated
with another mutex, and associated with an earlier acquisition when the checked
evidence supports that distinction.

## Technical obligations behind the human interface

The kernel needs generative initialization identities tied to storage lifetimes,
fresh acquisition identities, checked use loans, and a protected assertion held
exactly once. An abstract contract universally reasons about its input
identities. A call instantiates those identities with the caller's resources;
produced identities must be justified by checked transitions. Loop assertions
can existentially hide acquisition identity without hiding the obligation to
supply ownership.

On acquisition, shared protected memory is interpreted at a fresh state
satisfying its assertion. Old observations retain their old snapshots. No
particular scheduler order is assumed. A member may constrain the fresh state
only through the control's checked invariant; possession of one member does not
expose the population total or payload.

Declarations should supply reusable, checked resource summaries so ordinary
calls and diagnostics visit the relevant inputs and effects, not every mutex,
resource, or historical state. Diagnostic witnesses retain source provenance
when obligations/transfers are built. Rendering a message must not rerun search
or scan the whole project to reconstruct why a failure occurred.

The reference ownership-transfer rule is the
[Iris lock specification, slides 4–5](https://iris-project.org/tutorial-pdfs/lecture11-cas-spin-lock.pdf).
It separates the shareable lock description, exclusive lock token, and protected
assertion. Its basic interface does not include explicit destruction. The
lifetime loans and initialization generations above are additional C-specific
obligations, not claims that the tutorial already proves Click's design.

## Review decisions and handoff criteria

The current design direction is:

1. Use the names `mutex_live` and `mutex_use`. Both have implemented preserving
   contract forms; mutable protocol transitions remain future work.
2. Keep the existing ownership-clause vocabulary. Do not introduce a `uses`
   keyword or a general protocol-effect annotation.
3. Permit automatic checked lending and reborrowing, provided a failure prints
   the exact Click resource or fact required and identifies a relevant blocked
   loan when one exists.
4. Use preserved guard occurrences for continuity and consumed/produced guards
   for replacement. Do not add a separate surface continuity witness initially.
5. Lead semantic proof failures with `Requires <Click proposition or resource
   clause>`. English supplies context; it does not replace the obligation.

The remaining design work is the checked lifetime-loan and abstract-identity
rules, including returned guards and conditional loops. Their implementation
must support these contracts without strengthening ordinary wrapper semantics
or granting current-memory facts from obsolete acquisitions.

The implementation handoff should contain the accepted contract sketches,
operation rules, and paired positive/negative examples for preserving,
acquiring, releasing, releasing/reacquiring, conditional loop ownership,
worker lifetime, returned guards that retain a use loan, and stale observations.
Each negative example must pin the
program-level obligation and its source location, not just an internal error
string. Verification, expansion/reverification, profile, and audit must agree.

Keep the frozen C unchanged. Preserve the current green checkpoint until the
new semantic rules and their diagnostics pass the ordinary gate. This document
does not authorize implementing unresolved syntax choices or claiming that the
example diagnostics already exist.

## Shared lifetime-hold checkpoint

The loan ledger now separates possession of a live share from permission to
read a resource description. A lifetime binding names the exact loan, scope,
share, and backing occurrence; every use checks those identities against the
current ledger and participant. Holding that lifetime prevents scope closure
and ownership recovery. It grants no memory view, ownership, new share, or
recovery right. Transferring a share does not release its outstanding holds;
ending a reborrow remains blocked until its holds are released.

Existing borrowing composites use this lifetime path after separately checking
their viewed resource. View authorization and reborrow rechecking use the same
possession check, so scope, occurrence, and holder checks cannot drift between
these operations. The hold transition itself carries no stable-read assertion.
Tests cover mixed identities, transferred and split shares, pinned reborrows,
ended scopes, forged certificates, and deterministic scaling over loan counts.

The concrete mutex adapter below builds on this shared infrastructure. Neither
checkpoint exposes `mutex_use` in the surface language yet.

## Concrete use-loan kernel checkpoint

The kernel can now lend one concrete initialization's `mutex_live` owner into
the existing loan ledger. The mutex adapter selects the exact owned occurrence
and removes it from the current resource context before installing the loan.
The resulting opaque use binding names loan/share authority; it supplies no
stable view, payload memory, lifecycle ownership, or destruction right.
Ordinary stable-view lending still rejects mutex owners.

Acquisition through a use binding checks the current participant, live share,
and exact mutex initialization. It opens the protected assertion as usual and
places a lifetime hold in the acquisition's mutex-ledger entry. Release checks
the current guard and restored assertion before removing that hold. Updated
protected state is permitted: the loan does not freeze its bytes or values.
A failed release does not discharge the dependency. Protocol comparisons also
compare the guard's lifetime hold.

Recovery requires the matching loan receipt, the whole root share, the lender's
close/recovery rights, and no outstanding hold. It returns the escrowed owner
once. Splitting and transferring use shares use the existing checked share
transitions; collecting all shares still cannot close the loan while a guard
holds it. Another mutex, another initialization at the same address, another
participant, an ended loan, or a stale guard cannot substitute for the required
authority. Missing use authority has a structured diagnostic rendered as
`Requires owns mutex_use(mu)`.

This is a staged kernel adapter, exercised by transition and hostile-evidence
tests; ordinary C calls still acquire through `mutex_live`. The entry methods
remain internal until resource occurrences can carry use bindings through
contracts and workers. There is no new accepted surface syntax, implicit call
lending, worker-join integration, or escaping-guard transport
in this checkpoint. Abstract contract protocol transitions remain frozen.
Deterministic scaling tests check one lend/acquire/release/recover operation
against increasing numbers of unrelated mutexes.

## Use-reborrowing kernel checkpoint

A concrete use permission can now be reborrowed through the existing checked
scope transition. The child pins exactly the supplying share, retains its
backing occurrence, and refers directly to the original loan's escrowed
`mutex_live` owner. It receives no owner copy, stable view, or recovery right.
A direct root-loan identity avoids searching the chain of parent scopes when
a deeply nested helper acquires a mutex.

The child borrower can acquire only that original mutex initialization.
Acquisition puts its hold on the child's scope; the child dependency keeps
all supplying scopes open. Returning the child share is insufficient while a
guard or descendant still depends on it. Ending the reborrow requires the
lender's close right and the complete child share, then restores only the
pinned parent share. Only the original lending scope can recover ownership.
Sibling shares remain available, and ended child permissions cannot be reused
or replaced by a later child with the same printed mutex address.

Views and mutex use share scope creation, pinning, dependency, and closure
rules, while each checks its own authority. A stable view cannot be converted
to mutex use, and mutex reborrows cannot produce stable views. Tests cover
nested acquisition/release, cross-participant returns, outstanding guards,
forged parent identities and stale transitions, protocol freezing, and
multi-size scaling of deep reborrow chains.

These remain internal adapters. There is still no accepted `mutex_use` surface
syntax or automatic transport through contract resources, worker creation,
join, or returned guards. Ordinary C calls continue to require `mutex_live`,
and abstract protocol transitions remain frozen. The next boundary is binding
these permissions to resource occurrences and carrying them through contracts.

## Owned use-resource kernel checkpoint

Concrete use permission now has an ordinary owned resource occurrence, printed
as `owns mutex_use(mu)`. Its identity includes the exact loan and share; two
shares for the same printed address are not interchangeable. It has unit,
exclusive ownership, no view or persistent core, no memory permission, and no
`Count` observation. Ordinary exact resource matching, framing, and consumption
apply. Substitution preserves the concrete identity and its diagnostic address.

Lending exchanges the concrete `mutex_live` occurrence for this use resource.
Reborrowing exchanges the parent occurrence for a child occurrence; closing the
child restores the exact parent. Recovery consumes the root use occurrence and
returns the escrowed owner. Acquisition requires both the owned resource and a
live loan binding held by the current participant. A loan entry alone cannot
replace a missing resource, and a leftover resource cannot revive an ended or
pinned share. Outstanding guards still prevent closure and recovery.

Hostile tests cover missing occurrences, stale children, pinned parent facts,
duplicate ownership, invalid quantities, and attempted views. The existing
multi-size mutex round-trip test now exercises these resource exchanges too.
This remains internal kernel support: there is no accepted `mutex_use` surface
term, automatic contract lending, or worker transport yet. Thread confinement
explicitly rejects use resources until moving an occurrence also checks share
custody and guard dependencies. The next boundary is abstract use bindings and
checked contract transport, followed by worker return and escaping guards.

## Caller-supplied use-authority kernel checkpoint

The loan kernel can now establish the lifetime promise of a modular
`owns mutex_use(mu)` input without manufacturing a `mutex_live` owner. This
proof-entry root stores an abstract initialization description separately from
escrow. It has no close or recovery right, no stable view, and no memory access.
Only the original caller, outside the modular proof, owns the supplying lifetime.
Ordinary call sites must still use lending or reborrowing; they must never invoke
this assumption rule to satisfy a missing requirement.

A receipt retains the exact input root and entry participant. The preserving
return check requires its owned unit resource, the complete root share, and no
outstanding child scope or guard hold. Another root at the same printed address,
a split share, a child permission, or a resource held by another participant
cannot replace it. Returning an input does not close it or recover ownership.
Nested reborrowing uses the existing checked pin, transfer, hold, release, and
end transitions; closing a child restores the exact abstract parent permission.

Tests cover absent and duplicate resources, invalid quantities and views,
wrong participants, split shares, stale evidence, forbidden recovery, outstanding
guards, nested helper return, and deterministic scaling with unrelated roots.
This is a checked kernel boundary, not yet accepted surface syntax or automatic
contract transport. The proof-entry builder and call-site resource planner still
need to connect contract clauses to these roots, with precise missing-resource
diagnostics. Abstract acquire/release protocols and escaping output guards remain
separate work; the existing transition freeze stays in place.

## Synchronous use-call transfer kernel checkpoint

A checked transfer component now handles one selected mutex-use requirement.
It consumes an exact owned `mutex_live` occurrence by lending, or an exact owned
`mutex_use` occurrence by reborrowing. The caller retains its unrelated resource
frame; the helper receives only its new use occurrence. The transfer retains the
original source, both participants, and checkable entry evidence. It never
invokes the modular-input assumption rule to supply missing call-site authority.

A preserving return requires the helper's exact owned use resource and checked
loan transitions connecting that call's entry to its returned ledger. Returning
a different ledger with similar descriptions, omitting transitions, or introducing
modular assumption roots in the call body is refused. Transferring the share back
and closing its scope must pass the existing guard, child-scope, and full-share
checks. The component then restores exactly the original owner or parent use
permission. Other returned clauses remain separate for the surrounding contract
planner to check; they are neither granted nor silently discarded.

Tests cover owner lending, nested helpers from caller-assumed inputs, preservation
of unrelated resources, missing/duplicate/wrong-holder authority, divergent
histories, outstanding guards, stale returns, and forbidden input assumptions.
Deterministic multi-size checks cover unrelated frames and explicit certificate
deltas. This component checks loan/resource transport; it does not replace body
certification or check mutex invariant restoration on its own.

Surface `mutex_use` clauses and automatic contract-planner integration are still
pending. That integration must select exact clause occurrences, retain the body
loan evidence, and report missing resources using Click syntax. Abstract mutex
operations, returned guards, and worker transport remain separate boundaries;
the current protocol freeze is unchanged.

## Preserving use contracts are wired

The accepted surface form is `owns mutex_use(mu);`. A helper receives and
returns that permission, without receiving lifecycle ownership or an acquisition.
A synchronous caller supplies it by lending an owned `mutex_live(mu)` or
reborrowing an owned `mutex_use(mu)`. The ordinary contract planner performs the
checked exchange, retains entry and recovery evidence, and restores the original
source. Nested helpers and repeated calls compose with owned memory and stable
views. Abstract lifecycle owners can be lent too: their exact assumed identity
is escrowed and restored, never replaced by a concrete initialization.

Independent proof entry binds each primitive use input to a caller-supplied root.
An unbound surface description is not executable authority. Preserving returns
check the exact input resource and its complete share with no guard or child
scope remaining. The ordinary contract return checker verifies the returned use
occurrences before recovery discards them. Missing authority is reported as
`Requires owns mutex_use(mu)`.

This exposes no acquisition numbers or continuity witnesses. Named primitive
binders, `views`, counts, consumed/produced use permissions, worker transfer,
and abstract acquire/release transitions remain unsupported. The existing
protocol freeze is retained. The direct-clause surface is the supported path;
transport hidden inside declared wrappers still needs occurrence-aware binding.
Tests cover nested and mixed contracts, precise missing resources, invalid
access, lifecycle/acquisition non-implication, and storage reservations. The
integrated planner has deterministic scaling coverage over unrelated frames.

## Direct guard inputs have acquisition identities

Independent proof entry now binds each direct `owns mutex_guard(mu)` input to
one fresh internal acquisition identity. A preserving return selects the entry
identity, so another guard at the same address cannot discharge that obligation.
The same identity allocator serves runtime acquisitions and assumed inputs;
these namespaces cannot accidentally collide. Describing a guard still grants
no ownership, lifecycle permission, or ability to release it.

The binding requires an actual, unique, unit owned occurrence. Views, duplicate
occurrences, and execution states cannot be used to create assumed authority.
The entry binding stays available when a wrapper hides the guard, so unfolding
restores the same acquisition. Its description alone cannot establish `held(mu)`;
that still requires the actual owned guard. Indexed selection and immutable
binding identities avoid scanning unrelated resources during lookup and state
comparison, with deterministic lookup scaling coverage.

This changes no contract spelling. The protocol freeze remains: abstract
acquire/release, guard outputs, and occurrence binding inside initially hidden
wrappers still need checked transition rules. This checkpoint supplies identity
preservation required by those rules; it does not enable lock/unlock in helpers.

## Runtime acquisition selects checked use authority

The modeled `pthread_mutex_lock` transition now selects an owned `mutex_use`
occurrence when present, validates its participant, live share, and exact
initialization, and attaches a lifetime hold to the new guard. Otherwise the
existing lifecycle-owner path applies. An unbound description, a missing owned
occurrence, or a permission from an earlier initialization cannot authorize it.
Unlock consumes the guard, restores the invariant, and releases the hold.
The use loan cannot end or recover lifecycle ownership while the guard remains.

These runtime calls now retain their hold/release transitions in the checked
loan-call evidence chain. They transfer no ordinary call inputs and keep the
current participant. The evidence must connect the exact predecessor and
successor; an equivalent-looking restored state cannot replace that successor.
C-operation regressions check acquisition, invariant exchange, recovery refusal,
unlock, and destruction, plus stale authority and deterministic scaling.

This closes the runtime dispatch and certificate connection; it does not remove
the abstract-contract protocol freeze. The surface spelling is unchanged.
Abstract invariant descriptions, acquisition outputs, and escaping-guard call
recovery remain separate work before helpers can perform these transitions.

## Lifecycle inputs and use roots identify initializations

Direct `owns mutex_live(mu)` inputs now receive fresh internal initialization
identities at independent proof entry. Like direct guards, their descriptions
survive folding and nested preserving calls. A description alone grants no
ownership and does not initialize runtime storage. Replacing the input with a
new same-address lifetime cannot discharge its preserving return requirement.
Runtime initialization and assumed inputs use the same private identity
allocator, so their identifiers cannot accidentally collide.

Assumed `mutex_use` roots also record a fresh initialization identity in their
checked opening evidence. Reborrowing retains that identity; lifetime holds
check it. Each bound use resource includes both its share binding and its
initialization identity. This matters even when two branches allocate the same
share coordinates: their differently initialized use resources cannot replace
one another at return or supply one another's guard lifetime hold.

These two steps change no surface spelling. A new fixture combines direct
lifecycle ownership, wrapper transport, and use lending. Kernel regressions
cover same-address replacement, missing/ambiguous ownership, and sibling-root
substitution. Initially hidden wrapper inputs remain conservative; abstract
acquire/release and returned guards still require explicit protocol-effect
checking before the transition freeze can be removed.

## Opaque abstract protocol and balanced acquisition kernel

The kernel now has a sealed abstract protocol description backed by one actual
rooted `mutex_use` input and its initialization identity. An address, a use
resource description without ownership, another participant, or another root
cannot supply this description. Binding it grants no lifecycle ownership and
establishes no runtime initialization.

A second checked layer models a successful local acquisition and release of
that opaque protocol. Acquisition creates a fresh guard occurrence and pins the
use root with a lifetime hold. Release requires that exact guard occurrence and
its matching root, participant, initialization, and hold. It removes the guard
and releases the hold. Both transitions retain checked loan-call evidence.
Returning the preserved use input requires no outstanding guard or child scope.
Hiding or removing the guard cannot discharge its lifetime dependency.

The protected assertion remains opaque throughout: these operations add no
payload resource or memory fact and do not infer an earlier observation's
value. They describe successful transitions, not termination or absence of
blocking. Tests cover balanced operation, repeated fresh acquisitions, missing
ownership, cross-root and cross-scope receipts, unchanged payload authority,
evidence composition, and scaling over unrelated resources.

These are kernel components, not new surface behavior. Runtime dispatch remains
frozen for abstract contracts. Wiring it requires checking acquisition effects
at calls (including existing guard ownership), connecting declared invariant
interfaces, and handling escaping guards. No syntax or continuity witness is
added by this checkpoint.

## Checked protected-resource interfaces

Runtime publication now uses a shared kernel check for the selected resource's
installed declaration and the initialized mutex. The resulting interface
records the resource family, parameters, field schema, and mutex address. It deliberately excludes the instance binder and observed
field values: two observations of the same protected assertion describe the
same interface even when their values differ.

Publication additionally requires actual folded ownership of the selected
instance before moving it into escrow. A declaration or interface description
alone grants no payload authority. The C runtime dispatcher uses this checked
entry; the raw escrow operation is private to the mutex module.

This adds no surface syntax and preserves existing publication behavior. It
provides a reusable declaration boundary, not yet a contract association with a
particular initialization. Abstract helper acquisition still needs that
association, fresh observations, and checked call effects before it can expose
protected state.

## Protected interfaces retain initialization identity

Successful declared publication now retains its checked interface in the mutex
ledger, bound to the fresh initialization identity. Lock and unlock preserve
the same sealed binding; neither rechecks a declaration against an old observed
value nor creates a replacement interface. Destroy removes it, and publishing
again at the same address creates a different initialization binding even when
the resource declaration is unchanged. Both empty initialization and declared
publication also accept the empty ledger left by destroying the last mutex.

Loop protocol continuity now checks this binding as well as initialization and
heldness. The check compares shared binding identity in constant time rather
than traversing the declaration or unrelated resources. Regressions cover
balanced exchange, same-address reinitialization, replaced or removed bindings,
and deterministic scaling over unrelated resource frames.

This establishes the concrete association. Transporting it through abstract
contracts, constructing fresh protected observations, and checking acquisition
effects remain separate boundaries. No surface syntax changes here, and abstract
helper transitions remain restricted.

## Preserving use calls retain the concrete interface binding

When a synchronous preserving `mutex_use` call has a concrete mutex ledger,
its checked transfer now selects the initialization-bound protected interface
using the callee's canonical use permission. A same-address permission from a
different initialization is refused. Nested reborrows retain the initialization
and select the same shared interface binding; return checks the permission
against the retained binding before restoring the caller's authority.

This metadata grants no payload ownership and contains no observed payload
values. Abstract inputs without a concrete association remain opaque. The
existing missing-resource diagnostic names the selected source authority when
a concrete initialization does not match. No contract syntax changes, and
abstract helper acquisition exposes no payload pending independent-entry
association and fresh-observation rules.

## Balanced opaque acquisitions in preserving use helpers

A helper with `owns mutex_use(mu)` may now lock and unlock that mutex. The
runtime creates a fresh guard and an exact branch-local acquisition receipt,
pins the use scope with a lifetime hold, and retains checked loan evidence.
Unlock requires the actual guard occurrence and matching receipt. Hiding the
guard cannot unlock, acquire again, or discharge the local return obligation.
Returning or throwing with an acquisition created by the current participant
is refused; a nested helper may still preserve its caller's guard.

This path grants no protected resource or payload observation. Direct
preserving lifecycle and entry-guard contracts retain their restrictions on
init/destroy and replacing an entry acquisition. `held` remains unavailable
for opaque protocol inspection. There is no new surface syntax.

For this first acquisition-capable contract discipline, every synchronous use
call may acquire. The caller must supply an available matching concrete
initialization, or show that possible abstract entry guards are separate.
A separate guard-only footprint projection, computed once at entry, includes
guards hidden in wrappers and undecided match arms. Runtime-created receipts
have their own indexed footprints. Unknown aliases are refused conservatively;
a helper that only preserves a use permission cannot yet opt out of this
acquisition-availability restriction.

Both direct lock/unlock and modular use-call summaries invalidate the mutex's
representation bytes and reject conflicting stable storage loans. The summary
uses an explicit runtime-authorized storage effect, separate from ordinary
contract writes, so retained raw storage ownership cannot preserve stale byte
observations. Disjoint owned memory remains available and unchanged.

The protected-state boundary remains open: independent proof entry needs a
contract association between the use permission and its invariant, and an
acquisition exposing that invariant must create fresh observations. Shared
workers and escaping guards remain separate work. Conditional acquisition loop
assertions now have the bounded empty-mutex checkpoint described above.

## Remaining semantic implementation boundaries

The heap-retirement checkpoint does not make the remaining migration mechanical.
Three substantial semantic boundaries still need careful implementation and
hostile certificate tests:

1. **Storage and lifetime authority.** The exclusive `mutex_live` owner is implemented,
   including generative identity, fold/unfold, and preserving call transport.
   Initialization now establishes live, exclusive storage, and initialized
   bytes resist ordinary writes, including through abstract contract inputs.
   Scope exit now checks concrete initializations and conservatively refuses
   ambiguous symbolic ones. Concrete kernel use lending, reborrowing, and guard holds are
   implemented, including owned use-resource occurrences. `mutex_use` still needs
   wrapper transport, worker-join recovery, and escaping guards that retain the loan.
   Direct preserving contracts now have checked entry, call, and return transport.
   The current heap refusal is a conservative dependency check, not this
   resource protocol.
2. **Abstract guard transitions.** Contracts need generative initialization and
   acquisition bindings, preserving versus consuming/producing occurrences,
   and sound instantiation at calls. Named primitive binders should use that
   occurrence machinery, without becoming field-bearing wrapper instances.
   Replacing an entry acquisition or exporting a new acquisition remains
   restricted until this is checked. Balanced opaque use acquisitions do not
   replace entry acquisitions or grant protected state.
3. **Interference and loop abstraction.** Acquiring shared protected state must
   establish a fresh observation without reviving earlier-memory facts. Loop
   assertions need existential, possibly conditional acquisition ownership,
   rather than the current concrete-status comparison. The frozen parity source
   now verifies for an empty mutex with a direct conditional guard resource
   and locally owned lifetime. Payload-bearing and
   use-loan-backed loop assertions remain open, as does the shared-counter
   demonstration.

Exact concurrent counter results additionally need conserved contribution
accounting connected to the invariant. Existing `Count` does not itself supply
thread safety or a global-population observation. Atomic publication is a
separate memory-model extension.

Once these transition rules and adversarial examples are fixed, declaration
plumbing, precise binder/source diagnostics, documentation, and regression
coverage are suitable bounded implementation tasks. The whole concurrency
migration is not yet a routine implementation handoff.

## Declared runtime binders and named primitive authority

Runtime mutex binder schemas now supply names and transfer roles to ordinary
call-map validation. Initialization consumes the named `state` input and
produces `lifetime`; destruction accepts that lifecycle name. The kernel checks
the exact supported schema independently of parsing. Old `invariant` input maps
are rejected as unknown binders.

Preserving named `mutex_live` and `mutex_guard` helpers now use ordinary call
maps. Names are checked references to raw owned authority, not field-bearing
composite instances. Preservation requires the same initialization/acquisition,
including across repeated helper calls. Missing ownership, wrong mutex inputs,
stale lifecycle names, and attempted primitive unfold are covered by regressions.
Named preserving `mutex_use` inputs also use ordinary maps. A named lifetime
can supply a checked use loan, and a named use can supply a checked reborrow.
Each call selects the actual named authority, derives a scoped callee permission,
and restores the caller's original name after recovery. The permission alone
gives no protected payload ownership.
See [the complete contract design](mutex-resource-contracts.md) for the supported
subset and remaining association, storage, and protected-state work.
