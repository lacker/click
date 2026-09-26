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

Today, `mutex_guard(mu)` can occur in declared resource bodies. `owns h:
holding(counter)` can preserve a folded guard wrapper through a helper. The
helper cannot change mutex protocols. This is a conservative implementation
boundary, not the proposed final meaning of concurrency contracts.

The proposed next surface is:

| Surface | Status in this proposal | What a reader should understand |
| --- | --- | --- |
| `guarded_by counter->mutex;` | Keep the existing spelling | This resource assertion is the one this mutex protects. |
| `owns mutex_guard(mu)` in a resource body | Keep the existing spelling | This resource contains ownership of a current acquisition, not merely knowledge that the mutex is locked. |
| Direct named guard clauses, such as `owns g: mutex_guard(mu);` | Extend contract support; not supported today | The function receives and returns the same guard occurrence. |
| `consumes` and `produces` for guards | Extend existing clause semantics; not supported today | The function can surrender an acquisition or return a newly established one. |
| `mutex_live(mu)` | Proposed new built-in resource; name open for review | Lifecycle ownership of this initialized mutex, including responsibility for destruction. |
| `mutex_use(mu)` | Proposed new built-in resource; name open for review | Permission to use this initialization while its lifetime is guaranteed. It gives no payload access. |
| Acquisition numbers, protocol generations, ledger annotations | Keep internal | Source contracts should not need to name checker bookkeeping. |
| A new `uses` clause or general effect language | Do not add initially | First try expressing the capabilities through ordinary resource clauses. |

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

## A semantic choice that must not be hidden by syntax

The identity of a declared wrapper and the identity of an acquisition inside it
are different things. A wrapper's model can change; an existential ingredient
can be replaced when its body is reconstructed. Therefore, "returns the same
wrapper" does not automatically prove "never released this acquisition."

Recommendation:

- A directly preserved guard binder names the same acquisition on input and
  output. The kernel enforces this through ownership, not a held Boolean.
- Ordinary `owns h: some_resource(...)` keeps its ordinary resource meaning.
  Do not silently freeze all of its model fields or existential contents.
- When a client needs acquisition continuity, its contract must preserve an
  acquisition witness in its public meaning. A direct guard clause is the
  initial explicit spelling. A wrapper can promise continuity only when its
  declared model/contract exposes that relationship; Click must not infer it
  solely from wrapper identity.
- A replacement acquisition cannot preserve current-memory observations from
  the old critical section. Snapshot and authority checks apply even if a
  wrapper is reconstructed with the same visible fields.

This refines the earlier informal phrase "owns a wrapper preserves its guard."
The implemented opaque checkpoint is safe because it forbids every mutex
transition. Removing that prohibition requires resolving the distinction above.
The representation of a continuity witness in a wrapper is still an open design
choice; do not introduce epoch-valued model fields as an accidental solution.

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
2. **Need:** the exact fact, resource ownership, or lifetime guarantee required.
3. **Available:** a small relevant selection of facts/resources on this path.
4. **Why it does not suffice:** the specific mismatch, with source provenance.
5. A next investigation or proof step supported by the evidence, if one exists.

Locations below are placeholders, not claims about current fixture line numbers.
Names must be taken from the user's program and contracts. Internal identities
may be displayed as local explanatory labels such as "the acquisition at line
18" when ambiguity requires them; raw ledger IDs are not the primary message.

### Access without protected ownership

```text
Cannot verify this write at counter.c:<line>:
    counter->value = counter->value + 1;

Need: exclusive ownership of counter->value.
Available: permission to use counter->mutex.
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

Need: ownership of this acquisition, available to return to the mutex.
Available: held_state contains that guard in its Holding arm.
Unfold held_state to expose the guard before this call.
```

Only make this suggestion when the `Holding` arm is established. Otherwise the
missing requirement is the model/branch fact selecting that arm, not an
unconditional instruction to unfold.

### Missing restored invariant

```text
Cannot return counter_state to counter->mutex at counter.c:<line>.

Need: counter->value == completed.
Available: counter->value == previous + 1; completed == previous.
This path updates the C counter but has not established the matching
contribution update required by counter_state.
```

These available facts must be actual checked facts, not a guessed explanation.
The report names the invariant clause defining the equality. It does not
automatically recommend weakening that invariant or changing the C program.

### Destruction before a worker's use ends

```text
Cannot verify pthread_mutex_destroy(&counter->mutex) at counter.c:<line>.

Need: exclusive lifecycle ownership, with all uses returned.
Still outstanding: the use lent to worker second at pthread_create(...).
This path has joined first, but has not recovered second's use permission.
```

This can indicate a C lifetime bug or missing join/resource-transfer evidence.
Report the distinction as unresolved until the proof establishes which it is.

### An observation from an earlier acquisition

```text
Cannot establish counter->value == saved at counter.c:<line>.

Known: saved equals the value read before the unlock at counter.c:<earlier line>.
Missing: a reason the current value still equals that earlier value.
The mutex was released and acquired again; another worker may have changed it.
```

A historical fact remains true about its original read. Do not report that the
fact itself became false or was arbitrarily erased.

### A contract that promises the same guard

```text
Cannot establish the return requirement for g in helper's contract.

Need: the acquisition received as g on entry.
Available: a different acquisition, created by the later lock call.
The input acquisition was returned by the unlock at helper.c:<line>.
```

Whether the contract should describe replacement or the C should avoid releasing
the lock is a human decision. The diagnostic must explain the discrepancy first.

## Do not disguise every failure as a missing fact

The desired "need X here" explanation applies to semantic proof obligations.
It is misleading for other failures:

| Situation | Required explanation |
| --- | --- |
| Bounded search did not find a proof | Name the remaining goal and relevant premises; say it is not yet proved, not false. |
| Click lacks the needed rule | State the unsupported operation and the valid proof obligation that cannot yet be represented or checked. |
| Verification exceeded a budget | Identify the operation/phase and budget; do not invent a missing program assumption. |
| Internal checker/certificate inconsistency | Identify a Click failure and preserve a reproducible case; do not blame the C program. |
| A counterexample is established | Show the admitted path and violated requirement, distinguishing symbolic evidence from an executed test. |

For example, today's unsupported abstract guard opening should eventually say:

```text
Click cannot yet verify opening this guard at a function boundary.
The contract supplies the guard, but Click does not yet represent its
acquisition at abstract function entry.
This is a verifier limitation; no additional C precondition is suggested.
```

Printing `need: false = true` as a substitute for that explanation is unacceptable.
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

Human review should settle these before implementation is treated as mechanical:

1. Are `mutex_live` and `mutex_use` understandable names, or does their distinction
   need clearer wording? Both names are provisional.
2. Is ordinary `owns` syntax for a use permission sufficiently clear, given that
   it owns permission rather than the mutex or payload? Prefer documentation and
   a precise resource name before adding a new clause keyword.
3. Is automatic checked lending at a call boundary understandable? The contract
   must reveal the lifetime requirement, and failure messages must identify the
   owner/use loan that supplies or blocks it.
4. Does the direct-preservation versus existential-wrapper distinction need a
   surface continuity witness? This remains open; do not silently pick a meaning
   that makes existing ordinary resource contracts stronger.
5. Do the refusal examples contain enough information to discuss the C, contract,
   and proof without understanding Click internals?

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
