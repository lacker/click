# P1: Concurrency demo with thread ownership, mutexes, and publication

## Objective and violated invariant

Requested on 2026-09-15. Deliver basic concurrency support before launch,
following the completed basic-C++ milestone. Rbtree remains the main launch
demo. The intended additional claim is: **Click verifies memory safety, race
freedom, and functional safety properties of three small concurrent C
programs under one documented thread and memory-model profile.**

The purpose is to test the architecture early: thread-local proofs, resource
transfer, shared invariants, and synchronized observations must compose without
enumerating schedules or rewriting C into verifier-friendly sequential code.
A sequential proof must not authorize a concurrent access or preserve a
current-memory fact after another thread can invalidate it.

Three separate programs form one milestone. Disjoint workers alone would miss
shared mutation; mutexes alone would leave atomic publication untested. Each
program exercises a different boundary in the same production proof engine.
Small passing examples are necessary but insufficient evidence of scalability:
this milestone also requires modular rules and deterministic scaling tests.

## Resume here: 2026-09-22 handoff

The session's implementation is merged into `master` through `d3aa4cd8`
(`Preserve pointee const qualification on struct fields`). The complete
`scripts/check.sh` passed on that commit: 3,588 unit/documentation tests and
all 81 integration harness tests. The concurrency milestone remains open:
**the real pthread header import still stops before C create/join binding,
and the concurrent parent has not been verified.**

The [pthread binding design](../design/concurrency-probes/pthread-binding-design.md)
is accepted. Resume implementation from it, rather than reopening the surface
choice or merging the historical parked branch. The
[probe record](../design/concurrency-probes/README.md#compiler-import-checkpoint)
records the exact import progress and frozen-source provenance.

### Completed during this session

- Compiler-backed `x86_64-linux-userspace` imports now lock the C11, LP64,
  unsigned-char, pthread/POSIX profile, explicit include roots, driver,
  opened dependencies, and ABI observations. Sequential verification and
  expansion work through that path. Target/profile mismatch, changed headers,
  and stale locks are rejected; kernel import support is retained.
- Real-header gaps closed: optional trailing `int` on short/long spellings;
  distinct signed-eight-bit `signed char`/`int8`; explicit `signed int`;
  anonymous struct typedefs; standard integer specifiers in different orders;
  signed/unsigned 64-bit inline struct arrays; and bounded constant-expression
  struct array dimensions, including the original `cpu_set_t` expression.
- GNU `nothrow`/`__nothrow__` and `leaf`/`__leaf__` import on supported function
  declarations, including combined and repeated attribute groups. They add
  no exception, purity, callback-absence, or memory-permission proof facts.
- Pointer-to-const struct fields retain qualification through initializers,
  copies (including embedded fields), calls, sequential access primitives,
  checked loads/stores, and proof expansion. A `const char *` member can be
  reassigned; writes through it and implicit const removal are rejected.
  Mutable aliases can still change its pointee. Const is not stable-view
  authority. Top-level const members, const union fields, and qualification
  beyond the first pointer level remain unsupported; source address-taking
  that would require nested qualification is explicitly refused.

The regression names and original header shapes are in the probe record.
`mdtests/const_pointer_fields.md` checks assignment, copies, and mutable-alias
updates; the C unit tests also expand and reverify the new proofs.

### Completed next slice: portable modeled pthread binding identity

The explicit modeled-pthread runtime selection now binds conditional
client verification to Click's exact built-in `<pthread.h>`, canonical
create/join declarations, x86-64 Linux user-space target, trusted v1
specification and digest, and the initial null-argument and direct-worker
restrictions. The checked binding record is retained in verified selections;
its digest participates in proof-artifact and incremental-session identities.
Verify, profile, and audit report the runtime assumption. This work runs on
macOS without GCC or glibc. The frozen `fork_join.c` is unchanged, and its
ordinary worker proof verifies under the selector.
Projects can now place `{"target":"x86_64-linux-userspace","runtime":"modeled-pthread"}`
in a directory-level `click.project.json`, so the profile is selected once
for neighboring sidecars. Existing inline directives remain compatible and
conflicts are refused.

The binding refuses same-named declarations without built-in provenance,
local definitions, shadowing, incompatible redeclarations, nonnull attribute
or join-result arguments, stale session selection, prepared imports, and the
kernel target. An incomplete pthread attribute pointer declaration no longer
panics the C parser; indexing it receives a local diagnostic. The complete
`scripts/check.sh` passed on this slice: 3,598 unit/documentation tests and
68 integration tests.

### Current modeled create/join checkpoint

The checked C `pthread_create` call now issues a symbolic status and a
pending success/failure transition after checking the exact direct worker
contract, callback ABI, termination rule, task transfer, and handle output.
A scalar local may copy the status or be assigned before a later C `if`
chooses the outcome. An unrelated, owner-authorized external memory store may
also occur while the status is pending; its value survives either outcome.
Failure retains task authority; success holds one live
completion right and withholds the worker's resources and facts until the
checked C `pthread_join`. Source-level proofs for immediate and delayed
status checks and a disjoint intervening store verify, expand, and reverify
under the modeled runtime on macOS.

This is a narrow step toward Chunk B, not its acceptance. One create may be
unresolved at a time. Its guard retains changed authority and the checked
worker memory projection, then applies only intervening local or external
store operations on success; failure keeps the current parent memory. Broader
disjoint operations, external handle slots, multiple pending creates, branch
joins, scaling across unrelated children, and a complete proof of the
unchanged frozen parent remain. The real-header and native runtime binding
remain separate work.

Use the checked modeled binding to give ordinary `step` on the unchanged
`pthread_create` and `pthread_join` calls guarded create outcomes and one
completion right tied to the actual handle and child identity. The selected
direct worker needs its unique verified contract and exact termination
evidence. Transfer and recover resources only through checked C transitions;
do not introduce a proof-only spawn or run the worker sequentially in the
parent. Keep creation failure's resources with the parent and keep the
nonzero status guard until the C branch selects it. Add Mac-runnable positive
and hostile regressions, expand and reverify a successful proof fragment,
and use `scripts/check.sh` as the gate.

Real-header import remains an independent production-binding task. The bounded
Linux regression still stops at `/usr/include/time.h:49`, `struct sigevent;`,
with ``unknown struct declaration `sigevent` ``. Keep that regression and the
opened headers unchanged. A later Linux binding may finish full header import
or use a separately designed, checked declaration projection; either route
must establish exact declaration, ABI, and runtime identity before making a
Linux runtime claim. The observed Ubuntu GCC 13.3.0/glibc 2.39 is not the
selected Debian Bookworm GCC 12.2.0/glibc 2.36 profile.

### Important implementation notes

- Keep `branch { then { ... } else { ... } }` for actual C `if` arms.
  `outcomes` distinguishes checked call outcomes (currently normal/exceptional);
  no success/failure renaming or new proof split is needed for pthread create.
  Preserve delayed status tests as guarded authority until an ordinary branch
  or checked fact selects the case; do not enumerate all combinations.
- Use ordinary `step`, result binding, and the direct worker's unique verified
  contract plus exact termination evidence. Completion rights are internal,
  tied to the actual handle and creation identity. Do not add a public thread
  resource or proof-only spawn, or reinterpret `step(Contract)` as selection
  of a nested callback contract.
- Future C++ threading is part of the long-term scope. Keep task transfer and
  completion independent of pthread status codes, output slots, and `void *`.
  Separate child identity from current owner/handle storage so checked moves,
  captured callables, exceptional creation failure, and cleanup joins can be
  added later. Those C++ bindings and lifetime rules are not this slice.
  Creation failure preserves authority at the transfer boundary; it must not
  rewind earlier argument evaluation, moved captures, or construction.
- `mdtests/c_nothrow_local_write_call_boundary.md` retains an unchanged C
  reproduction of a separate limitation: an ordinary call cannot yet lend
  write ownership of its caller's local scalar. Keep that negative regression;
  do not rewrite the C or infer ownership from `nothrow`. The frozen thread
  demo uses external output ownership and shared local job views, so it does
  not require general exclusive transfer of implicit local storage.

Remaining sequence: establish the portable modeled binding identity (Chunk A),
bind actual C create/join steps and guarded completion evidence under that
explicit assumption (Chunk B), and verify the frozen parent with shared-reader
splitting and its companion (Chunks C/D). Then validate a native runtime
binding for each claimed platform and implement the separate mutex and
release/acquire programs. None of those production concurrency steps landed in
this session.

## Current checkpoint and scope

**Termination prerequisite complete.** Termination is now Click's only judgment for C (see "C
termination" in `docs/reference/language/index.md`), so a worker's contract
says whether it returns and a join on it can state what the parent proves.
A historical unfinished fork/join implementation remains on
`claude/concurrency-demo-slice2-parked`. Its `design/concurrency-probes/PARKED.md`
is failure history only; resume from current `master` and the accepted binding
design, not from that branch.

The source-selection checkpoint is
[`design/concurrency-probes/fork_join.c`](../design/concurrency-probes/fork_join.c)
with its [profile record](../design/concurrency-probes/README.md). It fixes an
ordinary C11/POSIX program, compiler/target/API choices, and creation-failure
paths before any thread rule or sidecar is written. The fixture is deliberately
not yet listed as a verifying example; its source bytes are pinned by the
examples gate.

The declaration-only import checkpoint is complete. `CTarget` now distinguishes
`x86_64-linux-userspace` from `x86_64-linux-kernel`, retaining this probe's
LP64 and `-funsigned-char` choices without injecting `__KERNEL__`. The narrow
modeled `<pthread.h>` declares `pthread_create` and `pthread_join` with a
`void *(*)(void *)` worker callback and a `void **` join-result slot; modeled
`<stddef.h>` supplies `NULL`. For the selected ABI, `pthread_t` is declared as
`unsigned long`. `pthread_attr_t` is deliberately incomplete because the
frozen program passes only null attributes. A regression parses the **unchanged**
probe and checks the declaration shapes; the kernel-target regression rejects
`<pthread.h>`. This work also added the C0 `void **` type, implicit assignment
from `void *` to a named struct pointer, and discarded direct calls written
`(void)call(...)`, all needed by that ordinary C source. These are source and
type support, not thread semantics.

The sequential worker checkpoint is complete. `mdtests/fork_join_worker_sequential.md`
proves the frozen `fill_range` byte for byte, in one thread, with the task
contract a spawn will later transfer: a `range_task` resource holding a view
of the job record, reached through the opaque `void *` argument by a contract
cast, exclusive ownership of exactly `output[begin..end]`, and the exact
filled-slice postcondition. Reaching this exposed and closed four Click gaps
with no C change: struct pointer casts of `void *` parameters in contract
clauses, certificates for quantified invariants whose symbolic range is empty
at loop entry, spelling memory reached through a loaded pointer field or a
cast parameter in synthesized certificates, and `contradiction` over an
introduced conjunctive guard. A sidecar directive
`target "x86_64-linux-userspace";` selects the user-space include model and
binds the target into artifact identities.

The caller-compatible worker checkpoint is also complete:
`mdtests/fork_join_worker_direct_contract.md` verifies the same frozen worker
with direct `views`/`owns` clauses, including expansion and reverification.
A caller cannot fold `range_task` for a job it owns, because folding a
composite whose body packages views over context-owned memory is refused by
the stable-views rules; the spawn boundary must therefore lend the job view
at the call, the way an ordinary call backs a callee's `views` clause.
Certificate synthesis now names fresh pointer-field values through the
worker's cast `void *` parameter or struct-pointer local. Loop initialization
also retains the checked guarded judgments of earlier invariants, so splitting
bounds into separate declarations does not expose extra internal implications
to a later universal proof. `mdtests/loop_three_invariant_initialization.md`
pins that case. These repairs add no thread semantics.

Loop exits now retain the kernel's declaration-indexed correspondence through
semantic deduplication and checked memory transports. Differently written true
invariants no longer shift a later universal onto the false guard.
`mdtests/loop_semantically_duplicate_invariants.md` verifies the original array
reproduction. Changed-state break exits do not assign exit spellings to old
loop-head facts. This repair also adds no thread semantics.

The internal ownership checkpoint now lives in `src/kernel/threads.rs`.
It uses the ordinary verified-call engine once to check a terminating worker's
entry and summary, retaining the output delta and postconditions behind an
opaque completion right. Failed creation preserves the complete parent path;
an empty or ambiguous worker summary is an explicit refusal. Join consumes
one right and recovers that worker's loans against the current parent ledger,
without restoring a saved frame, memory, or ledger. Two workers with disjoint
owned ranges and borrowed job views can join in either order. Kernel tests
cover overlapping writers, duplicate and foreign joins, missing or mismatched
termination evidence, withheld postconditions, pinned backing scopes, and
recovery work over 8, 16, 32, and 64 outstanding workers.

This checkpoint supports explicit ownership of external memory and nonescaping
views only. Exclusive transfers of caller stack/global/static storage are refused: ordinary
C accesses to that storage can bypass explicit ownership, so per-context storage
authority must be enforced before permitting such ownership transfers. The frozen
parent's output buffer is a caller-supplied parameter; its stack-resident job
records use local backing for stable views and lifetime checks through join.

The local-view checkpoint is complete, using existing `views` syntax. A live
local allocation can now back a checked loan without an explicit `owns` fact.
The kernel checks byte bounds, records the reader share and caller close right,
and blocks conflicting writes and allocation retirement until the loan ends.
Nested synchronous readers reborrow through the same bindings. Internal worker
spawn keeps the loan active through join; join closes it without fabricating
ownership. All scope-exit outcomes and retained lifetime certificates enforce
the check. This establishes local **shared-view** authority; it does not enable
exclusive transfer of implicit stack/global/static authority.
A second reader cannot yet reborrow an already pinned parent share; the shared
reader companion still needs explicit share splitting and recombination.
Composite/escaping borrowing, heap protocols, and counted-resource deltas are
also outside this internal slice. The scoped valid-join-success assumption is
explicit in the internal operation.

The modeled header is not a locked import of glibc headers. No C call site
invokes the internal operations yet: pthread declaration recognition, binding
the opaque right to the written `pthread_t`, ordinary result-status branching,
artifact integration, the concurrent parent sidecar, and verified concurrency
examples remain to be implemented. The numeric representation of `pthread_t`
grants no completion authority. Do not present the internal tests, a successful
parse, or native compiler syntax check as race-freedom evidence for the C probe.
The next modeled-runtime path must identify its trusted assumptions in every
client result and keep them distinct from native runtime validation.

Build on the authority conservation, stable borrowing, observation support,
and checked transitions in the [stable-views record](../docs/internals/stable-views.md).
The two-context and mutex experiments in `src/kernel/tests/loan_model_tests.rs`
are design evidence only; they do not implement concurrent C semantics.

The user-space target is available to normal verification, and compiler imports
now lock the actual selected driver, opened headers, flags, and ABI observations.
Conditional client verification may use an explicit, exact modeled-runtime
binding once its checked C transitions and artifact identity are implemented.
Before claiming that a native Linux or macOS build satisfies the proof, validate
that platform's actual declarations, ABI, and runtime specification against the
binding. A target name, modeled header alone, or generic compiler lock does not
identify a trusted native thread operation.
Use a coherent C11-compatible account of ordinary accesses, data races, thread
start/join, mutex synchronization, and release/acquire publication. Bind the
profile and modeled API identities into imports, certificates, and caches.
Reject unsupported operations or orders locally. Never strengthen a source
atomic order silently or substitute sequentially consistent execution for a
weaker source program without a sound justification for the selected subset.

Thread and mutex library primitives may initially have explicit trusted runtime
specifications. Their resource and synchronization rules must still be checked
by the kernel, and all three client programs and their worker contracts must
be verified. Clearly distinguish verified clients from assumed runtime
implementations; proving an OS mutex implementation is outside this milestone.
Recognize the actual selected declarations, types, and macro/builtin lowering,
not arbitrary functions that happen to have matching names.

Pick small ordinary C sources, check that they exercise the intended patterns,
and freeze them before writing the sidecars. Preserve source and provenance in
the example projects. Synthetic examples are acceptable when identified as
such. Do not add proof-only locals, branches, helper calls, identifier changes,
or serial execution wrappers to make their proofs work.

## Implementation handoff: remaining bounded chunks

Read this section together with `docs/internals/stable-views.md` and `AGENTS.md`.
Implement one green chunk at a time. Do not merge the parked branch; its
`PARKED.md` is historical evidence, and its saved-state join is not the design.
The frozen C remains `design/concurrency-probes/fork_join.c`. Do not edit it,
insert immediate status checks, or introduce proof-only locals or helper calls.

### What is already decided

- `views` means stable shared access. Stack-backed views use the existing
  surface syntax. A loan pins the allocation lifetime and forbids writes,
  including writes through aliases and same-value stores.
- An implicit local loan has no owned escrow. Ending it restores implicit
  access; it must not create a resource fact the caller did not supply.
- A worker needs a verified task contract and termination evidence for that
  exact worker. The internal operation refuses an empty or ambiguous summary.
- Creation failure preserves the parent path and task resources and creates
  no completion right. Success transfers the task and creates one linear right.
  The parent receives no worker postcondition until a checked join.
- Join consumes one matching right, composes only its output delta, and closes
  its loans against the current parent ledger. Never restore a captured parent
  frame, memory snapshot, or ledger. Preserve unrelated intervening work.
- The selected runtime assumption is success of a valid join on this parent's
  live terminating child. It is scoped evidence, not a theorem that every
  arbitrary `pthread_join` succeeds or every schedule makes progress.
- Keep data-race safety over execution prefixes separate from postconditions
  about completed operations. Do not enumerate schedules.

### Code map and completed regression boundary

- `src/kernel/threads.rs`: `ThreadContext`, opaque `ThreadHandle`, completion
  registry, spawn, and join. Start here; reuse its checked operations.
- `src/kernel/functions.rs`: `prepare_contract_resource_transfer` classifies
  implicit local views and uses the ordinary verified-call boundary. Explicit
  owners and existing views still take the ordinary lend/reborrow route.
  Local backing is checked against callee entry memory: by-value aggregate
  parameter copies are fresh allocations absent from the earlier caller memory.
  `mdtests/struct_conditional_value.md` pins that distinction.
- `src/kernel/loans.rs`: `LocalViewBacking` checks live allocation coverage;
  `StableViewTransferPlan::lend_local_views` emits checked local roots;
  `recover_suspended_views` discharges against the current ledger. The local
  root has a close right and no recovery escrow. Do not expose its backing
  constructor to surface tactics or replace it with unchecked ownership.
- `src/kernel/eval/statements.rs`: `end_scope_automatic_lifetimes` and
  `paths_after_scope_exit` reject live-loan retirement. `src/kernel/proof/execution.rs`
  checks the same rule when recording and rechecking lifetime events.
- `src/kernel/tests/thread_transition_tests.rs`: internal success/failure,
  both join orders, invalid completion, ownership overlap, local lifetime,
  withheld results, termination, and recovery scaling. The local test exercises
  normal, return, break, continue, jump, and exception exits.
- `mdtests/stable_view_local_job.md`: ordinary struct-local initialization,
  direct field views, a nested reader, and a later write. Its expansion
  regression in `src/surface/tests/expansion_tests.rs` rechecks simple proofs.
- `mdtests/fork_join_worker_direct_contract.md`: the frozen worker's reusable
  direct task contract. The output slice is external parameter memory; only
  the job record is stack storage. Do not block this demo on exclusive stack
  transfer, which it does not need.
- `RESOURCE_SEMANTICS_VERSION` in `src/kernel/mod.rs` is the authoritative
  current version. The local-loan/lifetime rule introduced version 3; later
  work has advanced it. Further authority or artifact interpretation changes
  must invalidate older artifacts.

### Chunk A: explicit modeled pthread binding identity

The [binding design](../design/concurrency-probes/pthread-binding-design.md)
keeps the ordinary `step`/`branch` author experience and direct-worker rule.
This first implementation chunk runs on macOS and uses the repo-owned
declaration projection under `x86_64-linux-userspace`:

1. Add explicit modeled-runtime selection tied to the exact built-in
   `<pthread.h>` provenance and digest, resolved external create/join
   declarations and types, target/ABI, trusted specification version, and
   null-argument restrictions. The model is a stated assumption, not an
   inferred property of any host pthread library.
2. Carry that identity and assumption through verification, retained
   certificates, incremental caches, profile, and audit. A result checked
   under the model cannot silently become a native-runtime result.
3. Test successful resolution and hostile lookalikes on macOS: local
   definitions, shadowing, conflicting types, incompatible redeclarations,
   altered headers, stale artifacts, and the kernel target. Keep actual
   worker/termination selection and thread authority behind the checked
   transition added in Chunk B.

**Acceptance:** focused Mac-runnable tests select exactly the intended modeled
declarations and refuse hostile ones; the assumption and binding identity are
visible and retained in artifacts; `scripts/check.sh` exits zero. This chunk
does not claim the frozen parent or a native pthread implementation.

### Chunk B: wire actual C create/join operations and their evidence

After A establishes the explicit modeled binding, route recognized C calls to
the shared checked thread engine. The evaluator and retained certificate
checker must use the same transition, including the handle store, return status, and memory
observations. Do not recursively execute Click or execute the worker body in the
parent. Reuse its verified summary once per application.

- On create failure retain the original parent continuation and resources. On
  success issue exactly one completion identity and havoc only the transferred
  mutable footprint. Reject overlap with the handle output store itself.
- Keep the child's output facts and resources inaccessible until join. Transport
  supported observations to current memory explicitly; an old snapshot may
  describe past values but cannot certify current mutable memory.
- Match join to the actual live right, consume it once, and recover only its
  output delta against current parent authority. Account for the optional
  result slot and its writable authority. Check the selected join assumption's
  scope and preserve the other child's loans in either join order.
- Retained events must bind predecessor authority, selected declaration/profile,
  exact worker/termination rules, arguments, handle identity, result case, and
  output delta. Forged surface certificates cannot bypass these checks.

**Regressions:** zero/nonzero creation, first/second creation failure, delayed
status testing, invalid/foreign/stale handle, duplicate join, copied handle,
wrong callback/argument/termination evidence, overlapping output/handle slots,
parent read/write before join, premature job scope exit, and withheld child
postconditions. Include forged evidence and cached-profile mismatch cases.
**Acceptance:** positive and hostile tests through actual unchanged C call sites
under the explicit modeled-runtime assumption; verify, expand, reverify,
profile, and audit agree under normal bounded tooling on macOS. No native
platform claim follows from this modeled result.

### Chunk C: shared-reader splitting and recombination

A single parent view is currently pinned by its first reborrow. A second worker
cannot reborrow that same pinned share. Build on the ledger's existing checked
split/join operations to distribute distinct reader shares and track their
common backing. Do not repeatedly create new roots from the same implicit
storage or duplicate one share into both workers.

Track outstanding shares by identity. Joining either worker returns only its
share; storage remains stable and live until every required share is back.
Recombine exact siblings before closing the root. A failed creation retains
its share in the parent. Two disjoint views of different job records already
work internally and do not require this extension.

**Regressions:** two readers of one range; both join orders; one create failure;
parent write/scope exit after only one join; duplicate/wrong sibling recovery;
nested reader; a fixed join among 8/16/32/64 unrelated readers.
**Acceptance:** a shared-read-only C companion verifies with no invented
ownership or user-managed fraction arithmetic; hostile recovery refuses locally.

### Chunk D: verify the frozen parent and complete the fork/join slice

Use the existing direct worker contract and local job views. Prove all three
source outcomes: first creation fails (four zeros), second fails after first
succeeds (join first, then `[11, 11, 0, 0]`), both succeed (join both, then
`[11, 11, 22, 22]`). Keep each stack job live through its associated join.

The output buffer is a parameter, so its disjoint `owns` slices use the existing
external-memory transfer path. Preserve the frozen C byte for byte. If a true
claim cannot be expressed or proved, reduce the Click gap and fix it; do not
specialize the C or weaken the required result. Move the source to a verifying
example only when this proof, the shared-reader companion, and hostile C
regressions pass under the explicit modeled-runtime profile. Document the
assumption and exact support boundary; native runtime validation remains a
separate requirement for a platform-specific claim.

### Native runtime binding after the portable client proof

Validate the selected Debian Bookworm GCC 12/glibc 2.36 declaration, callback
ABI, handle representation, and trusted pthread specification against the
modeled operation. A complete real-header import is one route; a typed,
checked projection of the actual declarations is another if it preserves
source and type identity without accepting lookalike functions. Keep the
bounded Linux real-header regression and fix its `struct sigevent;` gap when
pursuing the full-import route. A future macOS binding needs its own Darwin
target, SDK declaration/ABI validation, and separate artifact identity; this
x86-64 Linux model does not certify a native Mac binary.

### Separate extension: exclusive implicit-storage authority

This can follow the first demo; it is not a prerequisite for its stack **views**.
Keep exclusive transfer of stack/global/static memory refused until implemented.

Define context-local authority over the allocation/range independently of
explicit resource facts. Every ordinary read, direct assignment, pointer load
or store, aggregate copy, call effect, lifetime end, and loop havoc that can
reach transferred bytes must check it. Transfer removes parent access; join
restores only the returned range. Partition by allocation identity and byte
range, including aliases and pointer casts. Escaping a function must not leave
a worker using its automatic storage. Global/static initial authority and
cross-context discovery require an explicit policy; do not infer ownership
merely from a known block name. Decide that policy before enabling transfers.

**Regressions:** direct scalar and aggregate local access while transferred,
aliasing and partial ranges, global/static access by another context, same-value
stores, premature retirement, both join orders, and access restored only by the
matching completion. Measure fixed operations with increasing unrelated storage
as well as increasing explicit deltas. Surface ownership annotations alone do
not solve this implicit-access problem; the enforcement belongs in the kernel.

### Gates for every chunk and later work

Follow `AGENTS.md`: isolated worktree, ordinary verification before expansion or
profiling, prompt bounded failures, unchanged C, and `scripts/check.sh` exit
status as the full gate. Fix unstable tooling before extending the example.
Do not file new issue entries without explicit user authorization.

Keep authority operations indexed and persistent. Add deterministic curves at
8/16/32/64 sizes for growing explicit work and fixed operations amid unrelated
state. Do not scan all locals, resources, completion rights, or histories at
every step, deep-compare saved environments, or enumerate schedules.

After fork/join, implement the mutex counter and release/acquire publication
programs below using the same checked authority and observation framework.
Their protocols, runtime assumptions, and surface notation require separate
concrete designs. Do not treat stable views as permissions to read changing
atomic or lock-protected memory.

## Three required programs

### 1. Fork/join over a partitioned buffer

A parent initializes a fixed-size buffer, starts two workers that modify
disjoint subranges, and joins them before reading the complete result.
Prove each worker's exact memory effect and the combined final contents.
Worker proofs must be modular and reusable independently of their scheduling.

Spawn transfers the worker's required authority out of the parent; a checked
completion handle allows join to recover its postcondition and returned
resources exactly once. Include a companion regression for shared read-only
borrowing across workers: the backing allocation and borrow remain live until
the corresponding shares return.

Reject overlapping write-authority transfers, parent access to transferred
memory before join, duplicate completion recovery, and freeing or leaving the
lifetime of borrowed storage while a worker can still access it. Account for
the selected API's thread-creation failure behavior: failed creation must not
fabricate a child or lose resources. Document any explicit runtime-success
assumption used by a demo and check its scope.

### 2. Mutex-protected counter

Two workers each increment the same ordinary counter once under one mutex.
After both joins, prove that the initially zero counter is exactly two and
that the accesses are race-free. Avoid overflow in the chosen scalar type.

The shared lock handle grants permission to use the protocol; it grants no
direct access to the payload. A successful acquisition obtains a unique guard
and the protected resources. Unlock requires restoration of the invariant and
returns the resources to the lock. Contributions or equivalent auxiliary
proof state must connect the two worker postconditions to the exact final
count; the weak invariant "the counter is nonnegative" alone is insufficient.
Keep this bookkeeping in Click, with checked conservation rules.

Reject an unguarded increment, access using the wrong mutex or an expired
guard, duplicate guard ownership, and unlock without restoring the invariant.
Add a regression that reads the counter, unlocks, then reacquires: an old
local value is still that old value, but cannot certify the current counter
without evidence that excludes intervening updates.

### 3. One-shot release/acquire publication

A producer initializes an ordinary payload, then release-stores a ready flag.
A single consumer acquire-loads the flag and reads the payload only after
observing the publication. Prove that this read sees the initialized payload.
Use a one-shot flag with explicit initial state and no resetting or reuse.
The consumer may poll, but the safety claim must not assume polling terminates.

The atomic protocol must relate the observed publication to the producing
write and its resource transfer. An acquire load does not gain arbitrary
published resources merely because it is labeled acquire. Transfer exclusive
payload authority at most once; repeated observations must not duplicate it.
Later uses can retain previously acquired authority where the protocol allows.

Reject the payload-read proof if either required release/acquire edge is
replaced with relaxed ordering, if the payload is read before observing ready,
or if the producer accesses the payload after surrendering its authority.
If relaxed accesses are initially unsupported, retain their local unsupported
diagnostics and add kernel counterexamples showing that absent synchronization
cannot establish the transfer. Do not describe unsupported syntax as a proved
data race. Include repeated-observation and competing-claim counterexamples
against duplicating the one-shot transfer.

## Required model and checked operations

- **Thread contexts and spawn/join:** distinguish concurrent components from
  alternative proof branches. Partition live authority and recover only the
  actual completed child's resources; never combine alternative histories as
  simultaneous ownership.
- **Lock invariants and guards:** represent resources held by a shared protocol
  outside any thread's usable context. Opening requires the matching
  synchronization operation and unique guard; ordinary resource unfolding
  cannot manufacture exclusive access to shared state.
- **Atomic initialization, load, and store:** preserve source types, supported
  orders, initialization, and distinct observations. Keep protocol access to a
  changing atomic cell separate from stable `views`; do not weaken the existing
  stable-borrow meaning or allow mixed ordinary/atomic access accidentally.
- **Observation and lifetime support:** preserve local copied values and facts
  about past snapshots, but require current authority and synchronization
  evidence for current-memory claims. Lock acquisition and publication must
  obtain supported observations rather than revive stale snapshot facts.
- **Certificates:** check synchronization, authority conservation, protocol
  identities, and permitted interference at the kernel boundary. Tactics and
  lowering propose transitions; they cannot assume another thread's result or
  certify one convenient schedule as covering every permitted execution.

Write down why each rule remains valid in the presence of arbitrary compatible
other threads, and why the selected memory semantics justify it. Reuse
sequential reasoning over exclusively owned or stable borrowed memory. Audit
call effects, frame transport, loops, and lifetime endings at the new boundary;
do not make every ordinary load enumerate other threads or invalidate the
entire project's memory state.

## Scalability and ordinary proof workflow

Follow the [verification efficiency contract](../docs/internals/verification-efficiency.md).
Use indexed thread, protocol, resource, and event identities with persistent
local updates. Explicit simple proofs must check in approximately linear work,
up to indexing factors, in selected source, proof, and certificate size.
Schedule enumeration, all-pairs interference checks, full-state clones per
transition, and scanning unrelated event histories are not acceptable designs.

Add deterministic work-counter regressions at four or more sizes for:

- increasing independent workers and disjoint resources;
- increasing lock or publication operations and their explicit certificates;
- fixed operations surrounded by increasing unrelated threads, protocols,
  facts, and historical observations.

Keep the simple-proof curves separate from bounded smart search. Document what
each measurement counts and any explicit output-dependent cost. Tiny examples
or faster warm timings alone do not establish this requirement.

Route all demos through normal verify, profile, expand, and audit using the
shared bounded engine. Establish ordinary verification before profiling or
expanding. Expanded sidecars must reverify against the original C. Diagnostics
must identify the access, missing authority or synchronization, and relevant
source locations within normal bounds. Follow `AGENTS.md` if tooling fails.

## Deferred support and acceptance criteria

General atomic read-modify-write operations (fetch-add, exchange, and
compare-exchange), reusable publication protocols, arbitrary relaxed atomics,
fences, condition variables, detached threads, lock-free data structures,
memory reclamation, Linux memory-model/RCU reasoning, and C++ threading remain
in [concurrency-and-atomics.md](concurrency-and-atomics.md). Avoid representation
assumptions that require every publication to be globally unique or every
thread count to be fixed at two; the first checked protocol can be narrow.
Do not claim deadlock freedom, eventual visibility, termination under arbitrary
scheduling, or lock-free progress. Functional postconditions apply when the
relevant operations complete; memory safety and race freedom cover execution
prefixes, including executions that do not complete.

Completion requires:

- All three original C programs, modular sidecars, profile assumptions, and
  reproducible commands are checked in; their stated safety and exact-result
  claims verify through the normal CLI.
- The negative regressions above fail for the intended local reason. Hostile
  certificates cannot duplicate authority, reuse expired identities, invent
  synchronization, or carry stale current-memory observations.
- A durable design record explains thread/protocol state, the memory-model and
  runtime trust boundary, rule justification, reused sequential rules, and
  extension points for the deferred atomic operations and protocols.
- Deterministic scaling curves pass; verify/expand/reverification/profile/audit
  agree; required positive and negative fixtures join the normal gate.
- Existing C and C++ regressions and `scripts/check.sh` pass. Documentation
  states the precise support claim and limitations. Delete this issue and its
  list entry when implementation, regressions, and durable documentation land.
