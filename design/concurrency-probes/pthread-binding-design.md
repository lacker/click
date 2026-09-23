# Pthread calls as ordinary checked C steps

Status: design direction accepted, 2026-09-22; implementation order amended to
allow modeled-runtime client verification on macOS before native binding.

This is the binding design for
[Chunk A](../../issues/concurrency-demo.md#chunk-a-explicit-modeled-pthread-binding-identity),
not implemented concurrency support or a verified parent proof.

Implementation checkpoint: the [probe record](README.md#compiler-import-checkpoint)
records completion of the user-space compiler-import foundation and successive
real-header fixes through pointer-to-const struct fields (`d3aa4cd8`). The
remaining Linux parser boundary is `struct sigevent;` in `time.h`. The
[issue handoff](../../issues/concurrency-demo.md#resume-here-2026-09-22-handoff)
starts with an explicit, Mac-runnable modeled binding. The real-header gap
remains for later native runtime validation.

## Recommendation

A pthread call should feel like any other verified call: the worker declares
what it borrows and owns, `step()` executes the actual C operation, and
`branch` follows the actual C condition. Successful creation suspends the
worker's resources; join returns its resources and postconditions. Click
remembers the right to join in checked execution state, associated with the
C handle. The author need not create, name, or fold a proof-only thread token.

Keep the first binding to a direct, verified, terminating worker with one
selected ordinary function contract, null attributes, and a null join-result
pointer. These cover the unchanged `fork_join.c`. Keep indirect callbacks,
explicit task selection, nonnull result slots, and escaping child handles as
separate extensions. This restriction is on supported operations, not on the
number of workers or the placement of status tests.

The agreed design decisions are:

1. Use existing `step()`, scalar result binding, and `branch` syntax for this
   slice, with no new public thread resource or spawn tactic.
2. Store a success-conditioned completion right in execution state; preserve
   unresolved outcomes without enumerating their Cartesian product.
3. Require a declaration-specific runtime binding before enabling these rules
   in ordinary verification. An explicitly selected modeled binding produces a
   conditional client result with visible runtime assumptions. A native claim
   additionally requires a checked platform binding. A target name alone is
   insufficient for either result.

## What exists and what changes

The worker contract in
[`fork_join_worker_direct_contract.md`](../../mdtests/fork_join_worker_direct_contract.md)
already verifies. Its `views` clauses protect the stack job record and its
`owns` clause covers only the output interval. The internal
[`threads.rs`](../../src/kernel/threads.rs) checks spawn, failure, and join,
withholds outputs until join, and recovers against the current loan ledger.
It is explicitly not connected to C calls.

Click already offers three relevant interfaces:

| Existing interface | Use here |
| --- | --- |
| `step()` | Execute a recognized create or join at the C frontier. |
| `let r = step(callee(...), { });` | Name the scalar result of a call, including one inside a C condition. |
| `branch { then { ... } else { ... } }` | Prove both feasible C arms and check their continuation interface. |

Named callback contracts and `step(Contract)` currently select a contract for
the function being called through a pointer. At `pthread_create`, the called
function is pthread, while `fill_range` is an argument. Consequently that
syntax does not already select the worker contract. Ordinary call binder maps
likewise bind instances of the immediate callee, not a nested worker task.
We should not silently reinterpret either mechanism.

For the frozen source, selection needs no new syntax: resolve the actual
`fill_range` designator to its verified function rule and exact termination
rule, then instantiate its existing contract with `&first_job` or `&second_job`.
The C `void *` argument remains the actual pointer value; the logical task is
the checked instantiated contract and transfer plan, not another C argument.
Missing or ambiguous evidence is a local refusal, not permission to pick an
arbitrary applicable contract. Selection is indexed by function identity.

This is a semantic extension to existing proof syntax. None of the create or
join proof fragments below works on the current implementation.

## Why `branch`, not `outcomes`

`branch` currently follows a C `if`; `then` and `else` name the source arms.
For `if (rc != 0)`, `then` handles failure. For `if (rc == 0)`, it handles
success. Keeping that correspondence makes the proof readable beside the C.

`outcomes` currently separates the normal-return and caught-exception paths
of a checked call. A future `outcomes` with success/failure arms could split
an operation's possible results independently of a source condition, but that
would be an additional proof operation. This slice does not need it: creation
records conditional authority, and the eventual C condition gets an ordinary
`branch`. A delayed test does not force an immediate proof split.

The implementation may share checked case-handling machinery. Public names
should still tell the author whether they are following source control flow
or distinguishing an operation's outcomes. No naming change is proposed here.

## Candidate sidecar and the author's experience

Use the existing worker declaration and proof byte for byte, changing only
its `verifying` source to `fork_join.c`. The candidate sidecar starts with:

```click
target "x86_64-linux-userspace";
verifying "fork_join.c";
```

Include `range_filled` and the complete `fill_range` declaration/proof from the
linked worker fixture. The candidate parent specification uses existing syntax:

```click
int fill_parallel(int output[4]) {
    owns output[0..4];
    ensures result == 0 or result == 1;
    ensures result == 1 implies
        output[0] == 11 and output[1] == 11 and
        output[2] == 22 and output[3] == 22;
    ensures result == 0 implies
        (output[0] == 0 and output[1] == 0 and
         output[2] == 0 and output[3] == 0) or
        (output[0] == 11 and output[1] == 11 and
         output[2] == 0 and output[3] == 0);
}
```

This is a contract candidate, not a complete proof file. The modeled-runtime
binding also needs explicit selection; the `target` directive alone does not
select it. Its eventual spelling belongs to Chunk A and must be retained in
proof artifacts. The parent proof first steps its declarations and proves its
initialization loop using ordinary loop syntax. At the first create condition,
its proposed proof fragment is:

```click
let rc = step(pthread_create(&first, NULL, fill_range, &first_job), { });
branch {
    then {
        // The C condition is rc != 0: creation failed.
        step(); // return 0; all four cells still belong to the parent.
        simp();
    }
    else {
        // rc == 0: first is bound to the live completion right.
        // The parent has output[2..4], but cannot access output[0..2].
    }
}
```

The second create uses the same pattern. Its failure arm steps the C join of
`first`, then returns zero with `[11, 11, 0, 0]`. Its success continuation steps
both C joins and returns one with `[11, 11, 22, 22]`. The comments describe
checked state, not extra annotations the user must write. The complete proof
and the required arithmetic/separation evidence belong to implementation.

The ordinary frozen program keeps its immediate conditions. A separate future
regression must also use this ordinary C shape:

```c
int rc = pthread_create(&thread, NULL, fill_range, &job);
int saved = rc;
int unrelated = 7;
if (saved != 0) {
    return 0;
}
(void)pthread_join(thread, NULL);
```

The proof steps the declarations and uses the same `branch` and join step.
No new proof construct is needed to name a completion right. `saved` denotes
the checked value copied from the call result. Overwriting `rc` must not change
that association. A proven equivalent condition can select the same outcome;
a condition on an overwritten, unrelated value cannot. The diagnostic for an
unresolved join should say which create result still needs to be established.
This is a companion regression sketch, not an edit to the frozen source.

## The checked transition

Each recognized creation has an immutable event identity. Record the source
call, modeled or native runtime binding, selected worker and termination rules,
evaluated C arguments, task bindings, handle output location, and fresh status
value.
Evaluate C arguments once with the ordinary expression engine. Pointer/handle
stores must use its normal authority and alias checks.

| Outcome | Parent authority | Handle and completion | Worker facts |
| --- | --- | --- | --- |
| `rc != 0` | Original task authority and loans remain unchanged. | No child or completion right. Handle output is not usable as a new child handle. | None. |
| `rc == 0` | Suspend exactly the task's ownership and loans; havoc its mutable footprint. | Store a symbolic pthread value and bind it to one fresh completion right in this parent. | Retained behind that right. |
| Matching join | Recover only that child's returned authority and close its loans against the current ledger. | Consume the right once; return zero under the scoped runtime assumption. | Publish the child's checked postconditions with current observation support. |

"Unchanged" in the failure row describes task authority, not a guarantee about
the handle output bytes. Conservatively treat those bytes as unspecified on
failure unless the locked runtime specification establishes a stronger fact.
Check writable authority for the output slot before either outcome; do not
allow it to overlap the worker's borrowed or transferred footprint.

The create operation must check that the success task is valid whenever
success is possible. An invalid worker/precondition cannot be hidden by
choosing the failure outcome. Likewise a proof cannot simply assume success:
it must cover both possible statuses unless checked runtime evidence narrows
them. Failure changes no task authority and creates no child.

Start makes initialized borrowed job fields available to the worker under the
selected runtime specification. While it runs, exclusive transfers exclude
parent access and views forbid all conflicting writes and lifetime endings.
Join makes that worker's completed effects available. This reasoning covers
arbitrary compatible interleavings without enumerating schedules. It does not
establish scheduler fairness or unqualified pthread termination.

The valid-join-success assumption is explicit in artifact/audit metadata:
this parent's unique, live, joinable child, the exact terminating worker,
no detach, cancellation, competing join, or self-join. Unsupported APIs must
not acquire an external-call fallback that bypasses these checks. Keep this
runtime assumption distinct from the worker's proved termination.

## Handles are values; completion is authority

A copied C handle can identify the same child. It creates no second right.
Join through either checked copy consumes the one registry entry; another
join through either copy fails. Reusing the handle variable for another
creation cannot retarget an older copy or overwrite the older right.

Bind through the symbolic value and its creation generation, not the spelling
or address of the handle variable. Ordinary value-preserving copies and
checked aliases retain the association. An integer literal, arithmetic guess,
user-defined token, or merely equal machine representation cannot issue a
right. The initial binding refuses operations that lose the required identity.
Runtime reuse of a numeric representation after join must not revive a stale
handle. Certificate validation checks creation identity as well as C value.

A join needs no user-written completion argument. It resolves the evaluated
C handle through the indexed binding and checks that the right is live in
this parent and on this path. Child rights cannot escape through an ordinary
function contract in the first slice. A function may return only after its
children have been joined; scope exit separately checks every borrowed local.

## Delayed tests and branch continuations

The design requires a guarded delta for each unresolved create, rather than
two full parent states or all combinations of outstanding results. The delta
is indexed by creation identity, status value, and affected authority entries.
Its failure arm retains task authority; its success arm holds the suspended
task and completion. Conditional handle output and memory effects use the same
guard. The internal unconditional `ThreadContext` operations are building
blocks; this guarded representation is new work.

Until the guard is established, code can operate on disjoint parent state.
An operation touching a guarded range must prove its authority under every
feasible outcome or first establish the relevant guard. In particular, a
parent cannot read transferred output while creation might have succeeded.
A join requires success evidence. Unrelated steps do not split on pending
statuses, scan all children, or discard their conditional authority.

Branch refinement cites ordinary checked facts relating the condition to the
recorded status. `branch` can carry an unchanged guarded entry through a merge.
If the arms change an entry, join validates only the changed identities: it
may keep the same guarded entry, remove a right consumed on every applicable
path, or refuse the merge. It must not union live rights or silently drop them.
Initially refuse merges that would need a new arbitrary conditional resource
formula, naming the differing children. This permits delayed status tests and
the frozen early-return paths without committing to a general linear sum type.

Loop abstraction and ordinary call framing must preserve unchanged completion
entries and their dependencies. Refuse a loop or call interface that changes
or exports them until an explicit checked summary exists. Multiple unrelated
pending creates must remain compact; repeated statuses may not cause implicit
exponential proof execution. The user can always supply explicit case proofs
when the program's actual dependent behavior requires cases; checking work
then follows that explicit certificate.

## Future C++ threading

Supporting C++ threading is part of the long-term scope. Keep the reusable
kernel operation as starting a verified task with transferred resources and
recovering its completion once. Pthread status codes, output parameters,
`void *` arguments, and handle representation belong to the runtime binding.
They must not define the generic task or completion interfaces.

Four future uses constrain that boundary without adding implementation now:

| Future use | Commitment in this design |
| --- | --- |
| Creation reports failure through an exception | The core describes whether a child was created and which resources transferred. The binding relates that outcome to a return value or exceptional edge. |
| A thread object is moved | Completion identity is separate from its current owner and the storage holding its handle. A future checked move can transfer authority without creating a second right. |
| A worker is a callable object with captures | A task consists of verified invocation/termination evidence and its resource bindings. A direct function plus `void *` is the initial adapter. |
| Cleanup joins a child | Explicit calls and supported cleanup actions invoke the same checked join transition, with their own runtime preconditions. |

The first slice still requires a child to remain with its creating parent.
"This parent" is an initial supported ownership policy, not an immutable part
of child identity. Supporting transfer later will require explicit checked
rules; no ordinary assignment, function return, or C++ move gets those rules
implicitly. Likewise, the abstract creation outcome is not intrinsically an
integer test: the pthread binding supplies the relation to `rc == 0`.

The failure rule preserves resources at the task-transfer boundary. A future
C++ binding must separately account for argument evaluation, moved captures,
object construction, exceptions, and cleanup; failure must not restore an
earlier C++ program state. Each wrapper needs its own checked runtime mapping,
not an assumption that all thread APIs have identical behavior.

C++ syntax, thread-object lifetime rules, callable lowering, ownership moves,
and automatic joining remain later work. These commitments keep that work
possible without making it a prerequisite for the pthread probe.

## Bind the modeled runtime first, then validate native runtimes

The existing modeled header provides declarations only. The next chunk adds an
explicit trusted create/join specification and binds it to the exact built-in
header and resolved declarations. This path runs on macOS while retaining the
`x86_64-linux-userspace` source target. It proves the unchanged C client under
the stated create/join assumptions; it does not claim that the host's native
pthread implementation has been validated.

The modeled record contains the target and ABI, exact built-in header
provenance/digest, resolved external declarations and canonical types, the
trusted specification version/digest, supported null-attribute/null-result
restrictions, and scoped valid-join-success assumption. Select it explicitly;
the target directive, an include spelling, or a same-named function alone must
not grant authority. Reject local definitions, shadowing, incompatible
redeclarations, changed modeled headers, and stale artifacts. Carry its
identity and assumption through verification, certificates, caches, profile,
and audit. A native binding has a distinct identity and cannot reuse a modeled
result as an unconditional proof.

The compiler importer already supports kernel and user-space profiles with
checked locks and target agreement. Real Linux header preparation succeeds,
but parsing still stops at an incomplete struct declaration. Native Linux
validation remains necessary before claiming that a Debian pthread runtime
satisfies the modeled operation. A user-space compiler lock alone grants no
pthread semantics.

For a native Linux binding, extend the existing import lock and
`PreparedCImport` identity. Its proposed runtime-binding record contains:

- The source profile: C11, x86-64 Linux user space, LP64, unsigned plain char,
  selected GCC/glibc environment, and exact compilation flags.
- Existing driver/cc1, configuration, dependency, preprocessed artifact, and
  ABI-probe identities, including the selected opened pthread headers.
- The resolved external declaration identities and canonical types for
  `pthread_create` and `pthread_join`, including callback and pointer types,
  linkage, and relevant attributes. The selected declarations must originate
  from the locked runtime headers, not merely have matching names.
- The version and digest of the trusted pthread specification, the supported
  null-attribute/null-result restrictions, and scoped join assumption.
- Observed size/alignment of handles and pointers and canonical callback ABI.
  Source locations support diagnostics; they are not sufficient authenticity.

Recognize a native call only after validating this record against its prepared
import and resolved declaration. A local definition, shadowed name, different
type, unsupported attribute value, kernel target, changed header, or stale
profile must refuse the concurrency binding. Same-name redeclarations must
resolve to that same checked external entity; an overriding definition must refuse.

Full compiler import is one route to a native binding. If unrelated system
header constructs prevent that route, a typed, checked projection of the
actual selected declarations is acceptable with a concrete importer design,
source/type preservation tests, and the same profile invalidation. Do not
silently strip declarations or call the modeled header a glibc lock. Neither
route is a prerequisite for modeled-runtime client verification on macOS;
neither platform receives a native concurrency claim before its binding is
validated. A macOS claim additionally needs a Darwin target and a checked
binding to its actual SDK declarations and ABI.

The complete binding digest must participate in certificate and cache identity,
along with the concurrency semantics version. Reuse the existing invalidation
path and bump the affected artifact/resource versions when interpretation
changes. Copying a proof to another runtime profile must force rechecking.

## Certificates, diagnostics, and work bounds

Evaluator and retained proof checker call the same checked transition. A
create event retains its predecessor authority identity, exact declaration and
profile, worker and termination evidence, C arguments, status/handle bindings,
and checked output delta. A join event names that create and cites its current
right and success evidence. Never restore a saved parent snapshot.

Expansion must retain enough evidence to check the same worker selection and
status refinement without rediscovering them. Surface rendering uses ordinary
steps and checked branch facts; serialization retains internal event identity.
Internal process-global counters must be mapped to certificate-local identities,
not treated as stable identities across independent checks. Verify, expand/reverify,
profile, and audit must agree on the same artifact and runtime assumptions.

Diagnostics identify the C operation, missing authority or success evidence,
and relevant creation/loan location. Examples: "join requires successful
creation here", "child already joined here", and "job is still borrowed by
this child". Avoid dumping entire states or all unrelated children.

Use persistent maps for completion identities, handle bindings, status guards,
and authority dependencies. Guard lookup and refinement touch the named delta;
join touches the child's output and current affected ledger entries. No
whole-environment clones, registry scans, deep state comparisons, or Cartesian
branch expansion. Measure deterministic work at 8/16/32/64 sizes for increasing
explicit work and fixed operations among unrelated pending or live children.
Include repeated delayed status tests, handle copies, and both join orders.

## Alternatives and implementation acceptance

A public `Thread(task)` resource would resemble ordinary resources but would
need special unforgeable construction, conditional production, and handle
binding rules. It adds user bookkeeping without eliminating kernel machinery.
A proof-only `spawn` would duplicate the real C operation. Neither is needed
for the selected source.

Reinterpreting `step(Contract)` at pthread calls would make it select a nested
argument's contract where elsewhere it selects the immediate call. Prefer the
unambiguous direct-worker rule now. If future multiple/indirect worker tasks
need selection, evaluate an explicit nested selector such as
`step(pthread_create(...), { }, worker: Contract(...))`. This is deliberately
proposed syntax, not accepted syntax or a requirement of the first slice.
The selector would choose evidence only; the kernel would still check the
actual callback identity and exact worker termination. General contracts that
promise a result without terminating worker evidence remain insufficient.

Implement in these independently checkable increments:

1. **Modeled runtime identity on macOS:** explicit selection of the exact
   built-in declarations and trusted two-call specification, distinct artifact
   identity and visible assumption, and hostile lookalike/mismatch tests.
2. **One create/join through actual C:** guarded state and handle binding,
   success/failure and delayed-test companions, using the existing thread
   engine. Check copies, stale/foreign handles, wrong worker evidence, withheld
   postconditions, overlapping slots, parent access, and local lifetime exits.
   Include forged retained events and deterministic scaling regressions. Run
   these source-level regressions under the explicit modeled assumption on macOS.
3. **Frozen parent client proof:** all three results, ordinary proof tools,
   original source bytes. Shared-reader splitting remains the separate next
   chunk;
   mutexes, atomics, and exclusive transfer of implicit stack storage are not
   prerequisites for this binding.
4. **Native runtime validation:** check the exact selected Linux declaration,
   ABI, and specification binding through full import or a checked projection.
   Add a separate Darwin target and binding for any native macOS claim.

Each code increment needs focused hostile and positive tests, ordinary
verification before expansion/profile, and an exit-zero `scripts/check.sh`.
The design itself does not settle every future pthread operation. It settles
the ordinary author experience and exact authority boundary for this probe.

## First implementation slice: completed import foundation

The compiler-backed user-space import foundation is implemented. It verifies
ordinary sequential C fixtures, expands and rechecks proofs, locks the actual
driver/dependencies/ABI/profile, rejects stale locks and target mismatches,
and preserves the existing kernel import path. Include roots remain explicit
and inventoried. `tests/compiler_import.rs` exercises these boundaries.

The unchanged `fork_join.c` is prepared through real host GCC/glibc headers;
its bounded regression records the next parser refusal. The
[probe record](README.md#compiler-import-checkpoint) lists the successive
header constructs now supported. Continue that Linux import investigation
when pursuing native validation. The immediate modeled-binding work uses the
same frozen C with Click's exact built-in declaration projection and explicit
runtime assumption. Do not strip native headers or reshape the frozen C.

The host regression uses Ubuntu GCC 13.3.0/glibc 2.39. The selected Debian GCC
12.2.0/glibc 2.36 environment still needs validation. Import progress is not a
pthread runtime binding or a proof of the concurrent parent.
