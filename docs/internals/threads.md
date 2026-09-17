# Threads

This page is the durable design record for thread contexts and `pthread`
spawn/join in the kernel: what a worker's task is, what spawn transfers, what
join recovers, where the trusted runtime boundary lies, and why each rule is
sound in the presence of arbitrary compatible other threads. It covers the
first concurrent program, fork/join over a partitioned buffer. The mutex and
release/acquire programs appear here only as extension points.

The authority, borrowing, and call-boundary rules this design reuses are in
[stable views](stable-views.md); the contract interface and the trust boundary
are in [architecture](architecture.md); the scaling obligations are in
[verification efficiency](verification-efficiency.md). The frozen C source,
the selected compiler and API profile, and the scoped runtime assumption are
in the
[concurrency probe profile](https://github.com/lacker/click/blob/master/design/concurrency-probes/README.md).
The milestone that this design serves is
[`issues/concurrency-demo.md`](https://github.com/lacker/click/blob/master/issues/concurrency-demo.md).

The worker proof and the declaration-only import exist today. The spawn/join
transition, the parent proof, the hostile fixtures, and the scaling curves are
planned; the [regression map](#regression-map) marks each one.

## Meaning

A worker is an ordinary C function verified once, modularly, against its own
contract. `void *fill_range(void *argument)` is verified sequentially, with no
thread rule involved, and its contract is the task that spawn transfers: a
stable view of the stack job record reached through the opaque argument by a
contract cast, `(struct range_job *)argument`; exclusive ownership of exactly
the output slice `output[begin..end]`; and the exact postcondition, the filled
slice. Nothing in the worker's proof mentions threads, and nothing about its
scheduling is part of its evidence.

Spawn is the entry half of an ordinary call with the return half withheld.
Join is that withheld return half, installed later. This is the whole model:
there is one execution frontier, the two `pthread_create` outcomes are
ordinary status branches of it, and no schedule is enumerated. A concurrent
component is not a proof branch, and a proof branch is never treated as a
concurrent component.

The worker's task is spelled as direct `views` and `owns` clauses rather than
as a folded composite the parent hands over. A parent that owns its stack job
record cannot fold a composite whose body packages views over memory the
folding context itself owns, so the spawn boundary backs the worker's `views`
clause by lending, exactly as an ordinary call does, instead of transferring a
folded task instance.

## Laws

Every transition below preserves the stable-views laws, and these in addition,
with an arbitrary compatible frame and arbitrary compatible other threads
present.

1. One call, two halves: spawn's entry half and join's return half are the two
   halves of one contract application. No rule may install a return half that
   the matching entry half did not produce, and no entry half may be consumed
   twice.
2. Linear completion rights: a successful spawn mints exactly one right, and a
   join consumes exactly one. A right is a resource, not a value; equal
   `pthread_t` bits identify nothing.
3. Authority moves only on synchronization edges: the parent's authority over
   the transferred region leaves at the spawn edge and returns at the join
   edge. Nothing in between moves it.
4. No authority without a right: the return half is reachable only by
   consuming the right that its entry half minted, and a right names its
   suspension record by identity.
5. Failure conserves: a failed creation transfers nothing, mints nothing,
   loses nothing, and leaves only the handle cell unspecified.
6. Coverage: every access in every context is covered by exclusive or
   stable-shared authority held by that context at that moment. Race freedom
   is a corollary of this and law 3, not a separate check.
7. Prefix safety: memory safety and race freedom hold on every execution
   prefix, including prefixes with outstanding unjoined workers. Functional
   postconditions are claimed only where the corresponding joins complete.
8. Locality: spawn and join touch the named contract, the named resources, and
   one indexed suspension record. They never scan other records, other
   threads, or the parent's unrelated frame.

## State

Thread state lives beside the resource context and the loan ledger in the
checked state root, in the same persistent, indexed, opaque style: every
transition produces evidence bound to the exact predecessor state identity.

| Record | Holds |
| --- | --- |
| Suspension | Fresh identity; the worker's contract interface and its instance binders; the resources the return half produces; the `ensures` facts; the recovery evidence for the call's loans (callee shares, call-created scopes, escrows) named by ledger identity; the argument value and the resolved callback address. |
| Completion right | A kernel-builtin linear token resource, `joinable(t, worker, arg)`, owned by the parent, keyed by the fresh handle value `t` and naming one suspension record. |
| Handle binding | The symbolic value written into `*thread` on the success path. It is a key, never authority. |
| Index | A persistent map from handle identity to suspension record, in the `PersistentMap` of `src/persistent.rs`. |

The right is the only carrier of completion authority. Suspension records are
not reachable by search, by spelling, or by arithmetic on `pthread_t`: a
record is reached by consuming the right that names it.

## Transitions

| Operation | Evidence | Result |
| --- | --- | --- |
| Spawn, success path | The recognized `pthread_create` declaration, a null attribute argument, a resolved worker address with a checked contract, the parent's reservations and backable views | The entry half applied: requirements reserved, views lent, memory-effect havoc taken, handle written, one right minted, one suspension record created |
| Spawn, failure path | The same call with a nonzero result | The parent's resources exactly unchanged, no right, no record, the handle cell unspecified |
| Join | The recognized `pthread_join` declaration, a null result argument, exactly one matching right | The right consumed, the record's produced resources and `ensures` facts installed, the call's loans recovered |
| Refuse | A right that is absent, already consumed, or not minted here; a non-null attribute or result argument; an unresolved callback | A local diagnostic naming the access, the missing authority, and the source location |

## The spawn boundary

`pthread_create(&t, NULL, worker, arg)` is a checked kernel transition on the
recognized declaration, `ExternalCallSemantics::ThreadCreate`, not a
user-written external contract. Recognition is by the imported declaration
identity from the modeled `<pthread.h>` under the `x86_64-linux-userspace`
target, not by a matching name. A user contract for `pthread_create` cannot
produce a right; only this transition can.

On the success path the transition runs the worker's contract as an ordinary
verified call at the spawn point. The call-boundary planner does its usual
work, unchanged: exclusive (`owns` and `consumes`) requirements are reserved
first from the parent, then views are backed, here by a composite lend of the
caller's owned stack job record, and cross-clause conflicts are refused at
planning as proven overlaps. The declared memory effect is compared against
the checked view frontier the same way. What differs is only which half of the
result the parent keeps.

Spawn keeps the caller's frame during the call:

- the parent's residual resources, that is, what remains after the worker's
  requirements are reserved;
- the entry loan ledger with the call's loans left open, so the job record
  stays borrowed;
- the havoc of the worker's memory-effect region.

Spawn withholds everything the return half produced, into the suspension
record: the resources the contract produces, its `ensures` facts, and the
recovery of the call's loans. An ordinary call closes its loans and recovers
its escrows at return; spawn is exactly the ordinary call with that step
deferred to join.

Spawn then writes a fresh symbolic value into `*thread` and mints one
`joinable(t, worker, arg)` owned by the parent.

The failure path is the ordinary nonzero-status branch. The parent's resources
are exactly unchanged: nothing is reserved, nothing is lent, no effect is
taken, no record is created, and no right exists. Only `*thread` is
unspecified, so the parent may not join on it, and the right it lacks is what
refuses the attempt.

In this slice the attribute argument must be the null pointer constant and the
callback must resolve to a concrete function address with a checked contract.
A worker reached through a function-pointer local needs a named callback
contract and is an extension point, not a supported form.

## The join boundary

`pthread_join(t, NULL)` consumes exactly one `joinable(t, ...)` right, follows
it to its suspension record, and installs the withheld return half: the
produced resources enter the parent's context, the `ensures` facts become
available, and the call's loans are recovered, ending the call-created scopes
and restoring the escrowed owner of the job record.

Recovery is identity-relative, not state-relative. The record names the
callee's shares, the call-created scopes, and the escrows by ledger identity,
and join checks each against the current ledger. Intervening transitions, a
second spawn among them, add loans and change the ledger without disturbing
those identities, and the parent could not have ended a scope it holds no
close entitlement for. So joins in either order install their own record, and
neither join needs to know that the other happened.

Three refusals follow from the right alone. A second join finds no right,
because the first consumed it. A join on a `pthread_t` value that this parent
never received from a successful spawn names no record; the numeric bits carry
no authority, and no arithmetic on them produces a right. A non-null result
argument is refused locally in this slice: `retval` transport is an extension
point.

## Why the rules hold under C11 and POSIX

The model rests on the two synchronization edges the standards give, and on
nothing else.

Thread creation synchronizes-with the start of the new thread. The worker
therefore begins in the parent's state as of the spawn, which is exactly the
state the worker's contract is instantiated against, because the entry half is
applied at the spawn point. No later parent write can reach the worker's entry
state, because any such write is on the far side of that edge and the parent
no longer holds authority over the transferred region.

Termination of a thread synchronizes-with the return from a join on it. The
worker's writes are therefore visible to the parent only after the join, which
is exactly where the postcondition and the produced resources are installed.
Before the join the parent has no fact about the transferred region and no
authority to read it, so it cannot observe a value across an edge that has not
happened.

The one timing question this design settles is where the worker's memory
effect is havoced. It is taken at the spawn, before the worker has run. That
is sound because the moment is unobservable to the parent: from the spawn to
the join, the parent holds no exclusive authority over the effect region, and
whatever it still views is loan-protected and therefore stable. It is also
necessary: taking the havoc at the spawn is what prevents a current-memory
fact established before the spawn from being carried across it. A fact about
the pre-spawn snapshot survives as history, which is the ordinary distinction
between a retained snapshot proposition and a claim about the current cell.

Data-race freedom is a corollary, not a separate analysis. Every access in
either context is covered by exclusive or stable-shared authority held by that
context at the time of the access. A valid resource context is a partition, so
exclusive authority over a byte exists in at most one context; a stable view
guarantees that no compatible component writes the covered bytes while the
borrow is active, and the lender's write authority is suspended in an escrow
rather than duplicated. Authority moves only along the two synchronization
edges above. Two conflicting accesses would therefore require one context to
hold write authority over a byte that another context holds authority over at
the same time, which the partition excludes. No access needs to enumerate
other threads, and no ordinary load acquires a project-wide obligation.

The rules survive arbitrary compatible other threads for the same reason they
survive an arbitrary compatible frame: a component that holds no authority
over a byte cannot access it, and the laws are stated over the authority the
rule names rather than over the global state.

### The trusted runtime boundary

The pthread implementation is a trusted runtime, not a verified body. The
scoped assumption this design takes from the probe profile is narrow: a valid
joinable handle, held only by this parent, with no detach, cancellation,
competing join, or self-join, is assumed to join successfully. Each
precondition is enforced rather than assumed. Validity and sole possession
come from the right being linear, parent-owned, and mintable only by a checked
success transition. Detach and cancellation are outside the selected API
subset and are rejected at the declaration boundary. A competing join needs a
second right, which no rule produces. Self-join needs a right over the joining
thread itself, which no spawn mints.

Thread creation failure is modeled, not assumed away: the nonzero branch is a
real path with its own proof obligations, and it is one of the three parent
outcomes the fork/join proof must discharge.

### What is not claimed

Deadlock freedom, eventual visibility, termination under arbitrary scheduling,
and lock-free progress are outside this model. Functional postconditions apply
where the corresponding joins complete. Memory safety and race freedom cover
execution prefixes, including executions that never reach a join and
executions that end with workers outstanding. A successful parse of the
probe's declarations, or a native compiler syntax check, is not evidence for
any of these properties.

## What the model refuses

| Attempt | Refused by |
| --- | --- |
| Returning from the parent with a right still owned | The leaked-right check at the function boundary: an unconsumed linear resource cannot be dropped |
| Returning, or ending the job record's lifetime, with its loan open | The existing ledger rule that a scope with a live loan cannot end, which is exactly "the storage dies while a worker can still reach it" |
| Reading or writing the transferred slice before join | No resource: the parent's reservation moved that authority out at the spawn |
| Spawning the same task twice | Reservation at the second spawn: the exclusive requirement is no longer in the parent's context |
| Transferring overlapping write authority to two workers | The same reservation failure, from the partition invariant rather than from a pairwise interference search |
| Carrying a current-memory fact about the transferred region across the spawn | The spawn havoc over the worker's memory-effect region |
| Joining twice, or joining a handle no spawn minted | Linearity of the right, and the absence of a record |
| A hostile return half proposed at join | Kernel recheck of the installed delta against the exact suspension record and its predecessor identity |
| A non-null attribute or result argument, or an unresolved callback | Local unsupported-form diagnostics at the call |

## Complexity

Spawn and join obey the
[complexity contract](verification-efficiency.md#complexity-contract). The
relevant input `q` is the worker's contract clauses, the affected call
operation, and the resources actually named; the output `d` is the withheld or
installed delta. Spawn costs one contract application plus one indexed
insertion; join costs one indexed lookup plus the installation of that
record's delta. Neither scans other suspension records, other rights, other
threads' contracts, or the parent's unrelated frame, and the suspension index
is a persistent map whose update copies only a search path.

Nothing in this design introduces a schedule enumeration, an all-pairs
interference check, a full-state clone per transition, or a walk over an event
history. The known efficiency violation the design inherits is unchanged: the
loan-preserving havoc costs cells times symbolic loans in one block.

The deterministic scaling regressions this milestone owes must count verifier
work, at four or more sizes, over two axes:

- increasing independent workers over disjoint resources, that is, `N` spawn
  and join pairs over `N` disjoint output slices, which must stay
  approximately linear in the spawn/join pairs and their named clauses;
- one fixed join surrounded by increasing unrelated live threads, outstanding
  rights, ambient facts, and retained snapshots, which must stay flat.

Each sample records the work attributed to the named spawn, join, reservation,
and recovery operations, so a failed curve points at the responsible checker.
Absolute timings on the four-element probe corroborate; they do not establish
the law.

## Extension points

These are named so the first slice does not accidentally foreclose them. None
is designed here.

- **Mutex protocols.** A lock invariant owns resources held outside any
  thread's usable context; a successful acquisition yields a unique guard and
  the protected resources; unlock requires restoration of the invariant. The
  shared handle grants permission to use the protocol and no direct access to
  the payload, and ordinary resource unfolding must not manufacture exclusive
  access to shared state.
- **One-shot release/acquire publication.** An atomic cell protocol, kept
  separate from stable views, relating an observed publication to the
  producing write and its one-time resource transfer. Repeated observations
  must not duplicate the transfer.
- **Named callback contracts for workers.** Today the callback must resolve to
  a concrete function address. A worker passed through a function-pointer
  local needs a named callback contract to select the task unambiguously.
- **`retval` transport.** A non-null join result argument returns the worker's
  `void *` value and must transport it without granting authority the
  contract did not produce.
- **Detach.** Outside the selected API subset. A detached thread has no
  completion right and therefore no route to install a return half.

## Regression map

| Rule | Tests |
| --- | --- |
| The worker verifies once, modularly, with its task contract | `mdtests/fork_join_worker_sequential.md` |
| The selected declarations are recognized, and only under the user-space target | `modeled_userspace_pthread_declarations_parse_the_frozen_probe`, `pthread_projection_is_not_a_kernel_header` in `src/languages/c/tests.rs`; `mdtests/userspace_target_directive.md`, `mdtests/userspace_headers_reject_default_target.md` |
| The C source is fixed before any thread rule | `concurrency_fork_join_source_is_fixed_before_thread_rules` in `tests/examples.rs` |
| Abstraction boundaries for two contexts, shared readers, a mutex guard, and a thread-local cell | The `r27_` through `r30_` tests in `src/kernel/tests/loan_model_tests.rs`, which are model-only design evidence and not concurrent C semantics |
| Spawn success transfers exactly the requirements and mints one right (planned) | `spawn_success_transfers_exactly_the_worker_requirements_and_mints_one_right` |
| Spawn failure conserves and mints nothing (planned) | `spawn_failure_leaves_the_parent_resources_unchanged_and_mints_no_right` |
| Join installs the withheld return half once (planned) | `join_installs_the_withheld_return_half_exactly_once` |
| Linearity and identity of the right (planned) | `a_second_join_of_a_consumed_right_is_refused`, `a_handle_value_no_spawn_minted_joins_nothing` |
| Transfer conflicts fail at reservation (planned) | `overlapping_write_transfers_fail_at_spawn_reservation`, `a_second_spawn_of_the_same_task_fails_at_reservation` |
| Parent access and lifetime rules (planned) | `parent_access_to_a_transferred_slice_before_join_is_refused`, `returning_with_an_unconsumed_right_is_refused`, `returning_with_the_job_loan_open_is_refused` |
| Stale current-memory facts do not cross the spawn (planned) | `a_current_memory_fact_about_a_transferred_range_does_not_cross_spawn` |
| Hostile evidence at join (planned) | `hostile_join_payload_is_rechecked_against_its_suspension_record` |
| The three parent outcomes of the frozen program (planned) | `mdtests/fork_join_parallel.md`: both creations fail, the second fails after the first succeeds, and both succeed |
| Shared read-only borrowing across workers (planned) | `mdtests/fork_join_shared_reader.md` |
| Scaling (planned) | `spawn_join_work_over_independent_workers`, `join_work_is_independent_of_unrelated_live_threads` |
