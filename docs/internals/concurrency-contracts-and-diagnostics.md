# Concurrency contracts and failure explanations

Status: proposal for human review, not an implemented language specification.

The human review boundary is the C source, its contract, and an explanation of
each unproved requirement. A reviewer should not need to understand the mutex
ledger, certificate representation, or tactic dispatcher to judge those things.
This document puts that boundary before the implementation plan.

It refines the [resource-invariant design](resource-invariants.md)
and the [shared-counter protocol](https://github.com/lacker/click/blob/master/design/concurrency-probes/mutex-shared-protocol.md). Existing failure
classification is described in [proof-failure triage](../concepts/proof-failure-triage.md).

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
iteration. This is groundwork for lifecycle authority; it does not establish
storage lifetime or implement `mutex_live`/`mutex_use`.

The proposed next surface is:

| Surface | Status in this proposal | What a reader should understand |
| --- | --- | --- |
| `guarded_by counter->mutex;` | Keep the existing spelling | This resource assertion is the one this mutex protects. |
| `owns mutex_guard(mu)` in a resource body | Keep the existing spelling | This resource contains ownership of a current acquisition, not merely knowledge that the mutex is locked. |
| Direct `owns mutex_guard(mu);` clauses | Implemented for preserving helpers | Receives and returns the entry acquisition; all mutex transitions remain prohibited. |
| Direct named guard clauses, such as `owns g: mutex_guard(mu);` | Extend contract support; not supported today | The function receives and returns the same guard occurrence. |
| `consumes` and `produces` for guards | Extend existing clause semantics; not supported today | The function can surrender an acquisition or return a newly established one. |
| `mutex_live(mu)` | Agreed name for a proposed new built-in resource | Lifecycle ownership of this initialized mutex, including responsibility for destruction. |
| `mutex_use(mu)` | Agreed name for a proposed new built-in resource | Permission to use this initialization while its lifetime is guaranteed. It gives no payload access. |
| Acquisition numbers, protocol generations, ledger annotations | Keep internal | Source contracts should not need to name checker bookkeeping. |
| A new `uses` clause or general effect language | Do not add initially | Use ordinary `owns`, `views`, `consumes`, and `produces` clauses; preserve their distinctions. |

The examples below are proposed contract sketches. They are not passing Click
fixtures or promises that the current parser accepts every spelling. In
particular, named primitive guard/lifecycle/use binders need a precise extension
of the current contract interface; existing named declared-resource binders do
not by themselves implement this feature.

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

For the unchanged [parity program](https://github.com/lacker/click/blob/master/design/concurrency-probes/mutex_held_parity.c), the intended loop meaning
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
particular scheduler order is assumed. Counted contributions may constrain the
fresh state through checked invariant updates; possession of one contribution
does not independently expose the population total or payload.

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

1. Use the names `mutex_live` and `mutex_use`. They are still proposed language
   additions, not implemented resources.
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
