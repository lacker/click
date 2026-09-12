# P1: Give views stable borrowing semantics

**Status: design and implementation plan only. No implementation chunk has
started under this plan.** Expanded on 2026-09-11 against `31e6366e` to make
future work suitable for bounded, individually assigned Luna tasks. The
earlier evidence below keeps its original investigation base. Recheck symbols
and fixture outcomes at the implementation base; do not treat historical
observations as fresh test results.

This file is the implementation brief. Read the semantic design before taking
a chunk; the chunk cards name prerequisites, code boundaries, regressions,
and completion conditions. A dependency is a tested integrated commit, not
another agent's unfinished branch. The cards are future assignments, not
authorization to start agents or implement the feature now.

Navigation:

- [Decision and violated invariant](#decision-and-violated-invariant)
- [Current implementation evidence](#evidence-from-the-current-implementation)
- [Stability and scope protocol](#what-stability-means)
- [Detailed kernel and surface design](#detailed-kernel-and-surface-design)
- [Regression catalogue](#regression-catalogue)
- [Implementation chunks and dependency order](#implementation-chunks-and-dependency-order)
- [Concurrency and Rust design checks](#concurrency-and-rust-design-checks)
- [Final acceptance and coordination](#intended-regressions-and-acceptance-criteria)

## Decision and violated invariant

Requested on 2026-09-11. Investigation base:
`79411f40e838c61af87a4424a0d483044a30cf67`.

**Change ordinary memory `views` to mean a shared borrow whose covered memory
remains unchanged and allocated while the borrow is active.** Keep `owns` and
`views` as the main surface distinction. Introduce checked lending and recovery
of authority instead of deriving an independently usable view while retaining
a usable writer. A view is temporary stability, not permanent immutability.

The required invariant is: an active shared borrow of ordinary memory cannot
coexist with authority that another proof component can exercise to write,
free, or end the lifetime of that memory. Copying a view description must not
let its holder access memory after the borrow ends. This must hold across
calls, callbacks, resource abstraction, and eventually thread boundaries.

Current Click does not enforce that invariant. This is a design gap for shared
borrowing and concurrency, not evidence that today's sequential verifier
accepts false postconditions: its memory snapshots and checked effects track
intervening writes. C0 currently has no concurrency model. Do not claim that
changing views alone adds concurrent C or Rust support.

The recommendation supersedes the earlier investigation's advice to preserve
weak C views because valid C permits aliasing. The same C can be proved with
different contracts; the probes below demonstrate two such migrations.

This is P1 by explicit user direction: fix the core view semantics before
launch, using the small concurrency and borrowing checks below to assess the
design. The launch remains P1 -> minimum viable rbtree -> public launch.
Production concurrent C and Rust frontends remain later work. The separate
P1 [basic C++ issue](basic-cpp-support.md) exercises these resource rules in a
small additional-language frontend; the broader design lives in
[Supporting more languages](../design/supporting-more-languages.md).

## Evidence from the current implementation

Follow symbols rather than relying on line numbers:

- `src/kernel/primitives/resource_algebra.rs`: `access_mode_core` projects
  an owner to a view; `consume_memory_resource_fact` returns `Preserve` for
  a view requirement. `MemoryResourceAlgebra::pair_validity_error` rejects
  overlapping owners, but not owner/view overlap. `memory_write_range` and
  `memory_resource_fact_permits_write` look for owned range authority.
- The same file's `combine_memory_resource_facts` and
  `combine_exact_resource_facts` can absorb a view into its owner. A real
  outstanding loan must never disappear through this normalization.
- `src/kernel/functions.rs`: `prepare_contract_resource_transfer` and
  `evaluate_contract_return_resources` borrow through entailment, deduplicate
  returned views, and publish supported core projections. These paths need a
  checked loan transition, not an extra check only at direct stores.
- `src/kernel/primitives.rs`: `ResourceContextStorage::supported_by` and its
  reverse index track projections supported by an owned resource. These are
  useful implementation groundwork, but are not transferable shared loans.
- `src/kernel/proof/execution.rs` and `src/surface/proof/resources.rs`:
  observation and scoped opening project views from resource bodies. Freezing
  all such derived entries would inadvertently freeze ordinary owners.
- `src/kernel/eval/statements.rs` checks resource write authority for external
  memory. `prepare_contract_resource_transfer` also special-cases in-bounds
  views of caller-local storage. A future loan check must cover stack storage
  too; allocation or a `local:` block name must not bypass a live borrow.
- `docs/concepts/resources.md` explicitly says views do not prevent owner
  mutation and cannot alone support a folded fact about mutable memory.

Two positive migration probes ran through ordinary bounded `click verify`,
with exit status 0, using the existing verifier source at this base:

1. [alias-owned.click](../design/borrow-probes/alias-owned.click) verifies the
   unchanged [alias.c](../design/borrow-probes/alias.c), retaining `owns p[0..1]`
   and `requires p == q` but removing `views q[0..1]`. Ownership of the location
   authorizes both the store through `p` and the read through `q`.
2. [field-split.click](../design/borrow-probes/field-split.click) changes a
   setter's `views cell(n); owns n->value;` to
   `views n->next; owns n->value;`. Its C is copied unchanged from
   `mdtests/composite_piece_caller_frames_viewed_field.md`. The caller still
   owns the folded cell and proves `n->next == old(n->next)` after the call.

Reproduce from the repository root:

```sh
cargo run --bin click -- verify design/borrow-probes/alias-owned.click
cargo run --bin click -- verify design/borrow-probes/field-split.click
```

These establish that the demonstrated contract migrations work today. They
do not check the proposed loan rules or establish the cost of migrating the
whole corpus. The earlier weak-view alias probe remains historical evidence.

## What stability means

| Resource or operation | Required interpretation |
| --- | --- |
| `owns memory(R)` | Exclusive usable authority over the selected range; direct reads need no separate view. |
| `views memory(R)` | Shared, read-only authority for a borrow scope; covered contents and allocation lifetime stay stable. |
| Two views of overlapping memory | Allowed; readers need not prove disjointness. |
| Usable ownership plus an active independent view of overlapping memory | Incompatible. The lender may retain a recovery entitlement, not usable write authority. |
| Ownership and view of disjoint fields/ranges | Allowed; writes to the owned part preserve the viewed part. |
| An observation supported by ownership | Internal access to that ownership, with snapshot/support checks; not a separately transferable stable view. |
| View of a structural resource | Preserves its selected structure, memory dependencies, and advertised facts for the borrow scope. |
| Shared handle to a mutex or another mutable protocol | Preserves the protocol, not each payload value; accessing payload requires that protocol's checked authority. |

For ordinary memory even a same-value store conflicts with a view: stability
must exclude conflicting access, not just prove equality before and after.
Initialization writes, bytewise stores, deallocation, object-lifetime changes,
and opaque call effects must obey the same authority rules. Snapshots remain
necessary; after a borrow ends, its old observations do not automatically
become facts about later mutable memory.

A view freezes the range selected at borrow entry. It cannot silently retarget
itself when a pointer-valued field changes. Structural resource dependencies
must be covered by the borrow, and a view of a pointer cell does not by itself
freeze the pointee. Preserve existing bounds, initialization, and allocation
checks alongside authority.

## Recommended mechanism: scoped loans with checked access tokens

Use a lifetime-indexed shared loan. The following is design notation, not
Click syntax or an implemented kernel API:

```text
begin scope k                         -> Live(k, 1) + Close(k)
lend Own(R) into k                    -> View(k, R) + Recover(k, R)
split Live(k, q)                      -> Live(k, q1) + Live(k, q2)
                                        where q1 > 0, q2 > 0, q1 + q2 = q
read with View(k, R) and Live(k, q)    -> read covered memory; retain both
end with Live(k, 1) and Close(k)      -> Dead(k)
recover with Dead(k) + Recover(k, R)  -> Own(R), consuming Recover(k, R)
```

Lending requires evidence that `k` is active and moves the owned resource into
checked loan storage. `View` is a copyable description; `Live` is conserved,
splittable authority. All live shares for a scope total at most one. Ending
requires the close entitlement, full share, and all outstanding access/opening
obligations to be closed. If an access temporarily exposes underlying
resources, it holds its live share until those resources are returned.
Recovery happens exactly once
per lent resource. Scope identities are fresh; an old description cannot
become usable again when a later borrow starts.

This gives a concrete fork/join account: each reader gets a view description
and part of the live token. The lender cannot end the scope while a reader
retains its share. Joining and collecting the shares allows ending and
recovery. Merely deleting a view from one local proof context proves nothing
about descriptions or access authority held elsewhere.

The initial surface can leave `k` and token splitting implicit for ordinary
function/loop borrows. Use exact kernel-checked split/join certificates;
fractions are not runtime reference counts and need not appear in routine C
contracts. Keep permission shares separate from today's resource population
counts. D4 chooses a binary split/join tree for the initial representation;
the fractions here are explanatory notation. D5 specifies the remaining
registration, opening, and closure side conditions. Do not implement an
unbounded scan of pointers or view copies.

This protocol is informed by existing lifetime logics: RustBelt separates
type ownership and sharing, and ties access to live lifetime tokens;
VeriFast gives concrete begin/end, borrow, and fractured-borrow operations.
They demonstrate why copyable shared-reference descriptions can coexist with
controlled recovery. They are precedents, not a proof of Click's proposed
implementation. [RustBelt, sections 4-5](https://plv.mpi-sws.org/rustbelt/popl18/paper.pdf),
[VeriFast lifetime logic](https://verifast.github.io/verifast/rust-reference/lifetime-logic.html)

### Alternatives considered

- **Keep weak views and prohibit sending them to threads.** Potentially sound
  with an additional sharing mechanism, but it leaves ordinary views without
  the desired stability guarantee and makes Rust references use another
  concept. Prefer one stable surface meaning.
- **Require full fractional permission to write and any positive fraction to
  read.** A suitable substrate for ordinary shared memory. Fractions split and
  rejoin rather than duplicate freely. Alone this changes the current view
  choreography and does not express lifetime-indexed, copyable Rust reference
  descriptions; combine it with scoped loans where useful.
  [Permission accounting in separation logic](https://www.cs.cmu.edu/afs/cs.cmu.edu/project/fox-19/member/jcr/www15818As2011/permacct.pdf)
- **Keep the core law and reject writes when a local view is found.** Insufficient:
  projections already accompany owners, normalization can erase views, and
  copies may reside in another thread or abstraction. The borrowing transition
  must remove usable write authority and conserve recovery authority.
- **Make every view permanent.** Stable but prevents later mutation or
  deallocation; inappropriate as the default for temporary readers.

## Detailed kernel and surface design

### D1. Public meaning and the P1 boundary

The supported C surface keeps ordinary `owns` and `views` clauses. An input
view lasts from the checked call-entry transition through the checked
call-return transition. It is not shortened to the last syntactic load.
Ownership authorizes reads directly; a read through a second equal C pointer
does not require creating a second view.

P1 must implement stable shared loans, scoped recovery, nested read calls,
partial-range lending, ordinary resource abstraction, local/heap/global
protection, and the corresponding proof/call/loop rules. It must also permit
stable memory facts in a resource whose support consists of active views.
Ordinary sequential C remains the implementation target.

The checked design model must additionally cover context splitting for
threads, exclusive child reborrows, returned field loans, and abstract
mutable protocols. These extensions need not acquire Surface Click syntax
or production C/Rust execution in this issue. Keep their operations separate
from supported operations and identify which model transitions have actual
kernel counterparts. Passing their model tests does not mean Rust references,
concurrent C, mutex implementations, or a C memory model are verified.

Do not add explicit lifetime parameters to every ordinary C contract. Do not
add an alternate user-visible weak-view mode. Explicit escaping resource-loan
syntax is deferred; returning a C pointer value remains supported where its
ordinary C lifetime and the caller's permissions permit it. Returning a pointer
does not return a loan or extend the allocation's lifetime.

### D2. Non-negotiable laws

The later chunks implement these laws together. A local test of a `frozen`
flag is insufficient.

1. **Authority conservation.** A byte range's write authority is usable in
   one component, suspended in a loan, or transferred to another component.
   Suspending it never leaves another usable copy in a folded owner,
   implicit stack capability, callback frame, or remembered composition.
2. **Reader stability.** While a view has valid access authority, every
   compatible component is unable to write or invalidate its covered bytes.
   This includes equal-value stores, initialization, free/realloc, and
   lifetime end. It is an access restriction, not an equality check afterward.
3. **No view-to-owner entailment.** Recovering ownership is a state transition
   requiring closure evidence and the unique recovery entitlement. Neither
   entailment, normalization, folding, nor a pure theorem can perform it.
4. **Descriptor/authority separation.** Copying, dropping, or deduplicating a
   description changes no live access share and no recovery entitlement.
   Descriptions may survive a scope; their authority does not.
5. **Exact identity.** Scope, loan, allocation lifetime, resource occurrence,
   and support generation are semantic identities. Equal pointer spellings,
   equal resource terms, equal byte values, and reused local names do not
   identify them.
6. **Supported facts retain support.** An owner-supported observation is
   usable only through its current support. A loan-supported observation
   additionally needs the correct active loan access. A fact about an old
   snapshot remains a historical fact, never implicit authority over memory.
7. **Locality.** A valid update remains valid when an unrelated compatible
   frame is present. Rule checking touches the named authority and affected
   dependencies, with indexed access, rather than scanning the whole frame.
8. **No authority from unknown aliasing.** A consuming/lending partition must
   have checked separation or shared backing. Failure to prove overlap is
   not proof of disjointness. Two read requirements may alias.
9. **Branch conservation.** Alternative program paths may each reason from
   the entry resources. A join cannot add their capabilities together.
   Concurrent contexts require an actual disjoint capability partition.
10. **Checked orchestration.** Surface tactics, contract lowering, and smart
    search propose transitions. The kernel checks them independently against
    the actual predecessor state and its evidence.

For each operation below, document an inductive argument that it preserves
these laws, including its behavior with a compatible external frame.
Bounded enumeration is a regression technique, not an unbounded soundness
proof. The frame-preservation requirement follows the separation-logic
approach discussed in the [Iris notes](https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf);
the concrete representation here is a Click design proposal.

### D3. State representation and ownership boundaries

Use persistent, indexed state alongside the existing resource context. The
names below describe responsibilities, not mandatory Rust type spellings.
Do not put live capabilities in `PureFactContext`, ordinary duplicable
propositions, or surface-only metadata. They must participate in checked
resource-state transitions and proof-state identity.

| Component | Required information and owner |
| --- | --- |
| Scope record | Fresh semantic ID, active/ended state, root access-share identity, unique close entitlement, and directly registered loan/opening dependencies. |
| Loan record | Fresh ID, scope, selected family/resource, entry-selected footprint, backing authority identity/generation, and restoration destination. |
| Escrow | The actual suspended owned pieces, including the selected quantity of non-memory resources and any restoration recipe for their packaging. Not searchable as usable ownership. |
| View description | Loan ID and permitted projection/range; no independent read or write capability. Immutable descriptions may be shared. |
| Access share | A conserved capability for an active scope. It may authorize several descriptions in that scope, but cannot be duplicated across concurrent holders. |
| Recovery entitlement | A unique claim to recover a particular escrow after its closure conditions hold. It confers no access while suspended. |
| Supported observation | Exact owner occurrence or loan ID, support generation, memory snapshot/epoch dependencies, and any required access-share/opening evidence. |
| Opening obligation | The selected resource body/protocol opening, held access share, required closing resources/facts, and parent dependency. |
| Transition evidence | Rule, predecessor identity, consumed capabilities, created capabilities, range/guard proofs, support changes, and successor identity. |

Keep `CResourceSpec`'s validated term/access/quantity/role/snapshot envelope.
It describes a contract requirement; it does not itself carry a runtime loan
capability. Instantiate hidden scope bindings at a checked boundary.
`CResourceQuantity::Count` is a resource population quantity, not a lifetime
fraction. Do not overload it or make existing counted resources arbitrarily
divisible.

The existing resource store has occurrence IDs and persistent indexes.
Use occurrence/generation identity for authority that can be consumed and
recreated. An equal `CResourceFact` is not sufficient evidence that it is the
same authority. Counted normalized entries need explicit quantity residuals
or selected-unit provenance rather than pretending the whole population was
lent. Support maps keyed only by a fact must be audited at this boundary.

Store the loan ledger in the checked state root, or in an equivalent resource
carrier included in that root. It must be shared by ordinary evaluation,
modular calls, proof execution, and certification. An execution path cannot
update memory while a second, disconnected ledger says its ownership is
suspended. A future concurrent composition combines compatible capability
fragments against the same authority interpretation, not independent mutable
copies of an authoritative ledger.

The API should have this division of responsibilities. This sketch is
proposed internal pseudocode, not code to paste into the crate:

    propose_call_transfer(interface, entry, support_evidence)
        -> TransferPlan + UndischargedObligations
    check_loan_step(current_proof_state, proposed_step, evidence)
        -> CheckedLoanStep | LoanRefusal
    apply_checked_step(proof_object, checked_step)
        -> successor_proof_object
    authorize_read(current_state, pointer, byte_width, authority_witness)
        -> CheckedReadAuthority | AccessRefusal
    authorize_write(current_state, pointer, byte_width, authority_witness)
        -> CheckedWriteAuthority | AccessRefusal
    project_supported_observation(current_state, support, projection_evidence)
        -> SupportedObservation | ProjectionRefusal

Proposed steps cover Begin, Lend, ReborrowShared, Split, Join, Project, Open,
CloseBody, End, and Recover. Only the kernel creates checked results.
A checked result is bound to one predecessor state/transition identity;
reusing it against a different successor does not create another spend.
A cached result may
re-prove the same judgment but cannot duplicate the underlying resource in
one composition.

For ordinary direct reads an ownership witness is sufficient. For a borrowed
read the witness selects a descriptor and active access capability. Write
witnesses select usable ownership, never a recovery entitlement. Implicit
local authority must produce equivalent checked evidence. The lookup layer
may find candidate witnesses by index, but a boolean from surface lowering
cannot be accepted as the witness.

The transfer plan should record, by contract clause: the evaluated term and
entry snapshot, selected owner/loan occurrence, any range split/coverage
evidence, caller residual, callee authority, scope binding, returned-access
obligation, and packaging restoration evidence. Common call/return code
consumes this record. Do not independently recompute a second mutable
footprint or independently rediscover which loans to recover on return.

Use structured internal refusals for unavailable authority, stale scope,
wrong share, unresolved/proven overlap, active opening/child, missing return,
invalid restoration, and unsupported escape. Existing public runtime/proof
errors can wrap these categories. Keep the checked result and refusal types
opaque outside their validating module.

### D4. Access shares: a concrete first representation

Use a checked binary split/join tree for live access shares in the first
implementation. The fraction notation above explains the semantics; arbitrary
rational arithmetic is not required. A root token represents the full share.
Splitting consumes one leaf capability and creates two fresh sibling
capabilities. Joining consumes those exact two siblings and recreates their
parent capability. Only the reconstructed root can close its scope.

Each tree node has an interned ID and constant-size parent/child links.
Splitting an already split or unavailable leaf fails. Joining repeated leaves,
non-siblings, leaves from another scope, or an ancestor with its descendant
fails. The active capabilities form a disjoint frontier of that tree.
A read checks the active leaf and scope by indexed identity; it does not
walk to the root. Repeated halving must not store increasingly long bitstrings
or denominators in every token.

This deliberately gives a simple sufficient sharing discipline. Arbitrary
real/rational fractions, reassociation of unrelated roots, and a symbolic
fraction solver are unnecessary for P1. A caller can split and return a
leaf for each nested reader. Collecting a split subtree costs the explicit
join operations in its certificate. General fraction syntax, if later
needed, must preserve these conservation and complexity properties.

Add a unique close entitlement separate from the root access token. Holding
all access shares allows reading; closing also requires ownership of that
entitlement and satisfaction of the scope's obligations. This keeps authority
to use a scope separate from authority to retire it. The initial caller
retains close/recovery entitlements while lending access to a callee.

Capabilities are conserved even if the implementation's persistent data
structures are clonable. Cloning a proof state creates alternative proof
paths, not two resources that may later be composed. If a share is discarded,
the program may lose the ability to recover; the checker must not reconstruct
the missing share from a reader count reaching zero. Do not make recovery
depend on Rust host-language destructors or garbage collection.

### D5. Transition rules and side conditions

The operation table is the contract for the kernel implementation. Every
refusal leaves the predecessor state unchanged; failed candidate search must
not partially consume authority or advance the published scope state.

| Operation | Required evidence | Result |
| --- | --- | --- |
| Begin | Fresh scope identity rooted in this checked execution | Active scope, full access token, unique close entitlement |
| Lend owned piece | Active scope, capability authorizing registration, usable ownership, checked range/quantity selection | Selected ownership in escrow, recovery entitlement, scoped description; untouched residual stays usable |
| Reborrow shared piece | Fresh child scope, active parent description/access, checked coverage | Child description and a dependency holding parent access until child closure; no duplicated escrow ownership |
| Split access | Available leaf for an active scope | Consume leaf, produce two fresh siblings |
| Join access | Both available siblings from the same split | Consume siblings, restore parent |
| Project description | Checked subrange/body projection from an existing description | New description with the same loan and required dependencies; no new share |
| Read through view | Active matching scope, available share, valid description/backing, range coverage and normal memory checks | Loaded value and snapshot evidence; same authority afterward |
| Open borrowed body | Available matching share and checked family sharing rule | Scoped body access and a pending close obligation holding that share |
| Close borrowed body | Required body resources/facts restored with unchanged protected support | Discharge opening, return held share |
| End scope | Close entitlement, full root share, no open accesses or dependent child scopes | Consume close/access authority; mark scope ended; release any access pinned from parents |
| Recover | Ended matching scope, unique recovery entitlement, intact escrow/restoration obligations | Consume entitlement/escrow; restore owned resource exactly once |

Registering a loan requires actual usable authority; an active-scope marker
alone is not authority to lend. For P1 a boundary creates its fresh loans
before dispatching their access. If a nested call needs another independent
owner, open another scope for it. Do not extend an already distributed scope
through an unchecked side channel. The model may later generalize registration
with an explicit extension rule.

The scope can own several disjoint escrow pieces. Ending it is not recovering
each one; recovery is separately checked per entitlement. Index its direct
obligations and escrows so the end transition does not scan every past
descriptor. Closing work may be proportional to the explicit objects being
closed, and recovery to the explicit pieces being restored.

Scope IDs must never be reused within a proof identity domain. Use fresh IDs
with provenance from the checked execution/fork; two branches that choose
the same numeric local counter must not accidentally name the same loan.
After closure, historical descriptions can be retained without retaining a
live capability. Retire unreachable bookkeeping when possible; preserve the
certificate identity needed to reject stale evidence. Do not keep all dead
descriptions in the hot lookup set forever.

### D6. Footprints, aliasing, and recovery of packaging

Select memory at entry as allocation-lifetime identity plus a checked byte
range and its source-level view. Preserve element width and existing
overflow/bounds rules when translating field or typed-array ranges. Overlap
must be checked in bytes: an int-sized owner and a byte view can conflict.
Store evaluated pointer identities; do not recompute the footprint from a
mutable pointer field when the call returns.

An empty range grants no dereference and protects no bytes. Preserve the
existing language rules for forming the range; do not infer nonnullness or
a live allocation from an empty permission. A nonempty subrange loan prevents
freeing or reallocating its entire containing allocation, even if unrelated
bytes remain owned. A loan's protection of allocation lifetime is not an
allocation/deallocation capability.

Partition an owned range when lending only part. For example, lending
`a[2..4]` from `owns a[0..8]` leaves `a[0..2]` and `a[4..8]` writable.
Recover only `a[2..4]` and normalize compatible owned residuals afterward.
Sibling fields that occupy distinct bytes remain independently writable.
A view of a pointer cell protects that cell; it does not recursively protect
the pointee unless the resource body explicitly includes it.

Two overlapping read requirements should use shared backing, not attempt
to escrow the overlap twice. For identical requirements, create one loan
and two descriptions. For partial overlaps, use a checked union/partition
of the required ranges or a covering existing owned range whose lending
does not suspend other authority promised by the same contract. Retaining
the unrequested owned remainder is the preferred behavior.

Do not require the caller to decide whether two read-only symbolic
parameters are equal just to pass both. It is sufficient to establish that
both descriptions are covered by the selected loan backing, allowing
overlap. When independent owned sources supply them, their composition
already supplies separation evidence. A general symbolic union requiring
case analysis may use explicit checked cases; silently assuming separation
or lending twice is forbidden.

Loan backing and resource packaging are separate. Lending from a folded
owner may expose only the selected body frontier and suspend the parent
head's independent usability. Keep a restoration recipe for the remaining
pieces and their facts. A parent cannot stay usable as a second route to the
escrowed bytes. Reassembly after return must check the body's advertised
facts in the resulting state; a disjoint permitted write may require
updated model arguments or a new fold proof. Do not restore a pre-call
composite fact just because its memory permissions were returned.

### D7. Read authority versus observations and pure facts

An owner may read directly and inspect its composite without issuing a
stable loan to itself. Replace the ambiguous owner-to-view projection with
an explicit supported-observation interpretation. Reading through that
observation checks its owner support; it cannot satisfy a transferable view
requirement without the checked lending transition.

A borrowed composite's observations retain loan identity and scope access.
Projection, fold, unfold, `open`, `close`, exact-resource normalization,
symbolic range splitting, and callback-fact extraction must preserve that
dependency. Identical descriptions may share storage, but descriptions
from different scopes cannot be merged by dropping one scope's conditions.
Combining an owner and a live borrowed description cannot absorb the loan.

There are three different proof outcomes:

- A copied scalar value or a proposition about an explicitly recorded old
  snapshot may remain true after a loan ends.
- A claim that the *current* cell still has that value requires checked
  framing from that snapshot, using active support or a proved disjoint
  effect. A later overlapping write blocks that transport.
- Permission to load the current cell requires current usable authority.
  Neither of the preceding propositions creates it.

Audit `CResourceComposition` and remembered premises as well as explicit
resource entries. A theorem about an old resource context can be retained
as historical evidence; it cannot reinstall a consumed access token,
authorize a current store, or manufacture a scope-close transition.

For stable facts in resource bodies, extend the current memory-coverage
validator only after the kernel carries support dependencies through every
resource operation. A schematic body containing `views p[0..1]` and
`fact p[0] == 0` may be folded while its access is active. Its hidden support
bundle must keep the required access or opening obligation. It cannot export
an apparently unscoped resource containing that fact and then let the lender
recover the bytes. No theorem may erase the bundle.

Static validation establishes that the declared footprint can cover the
fact. Dynamic folding also proves the fact, valid current access, and
dependency capture. Static coverage alone does not justify the assertion.
Track dependencies reached through nested resources and predicate definitions;
retain existing guard/bounds checks and bounded explicit unfolding behavior.

### D8. Function entry, call planning, and return

Ordinary function-body certification starts from a generic contract context.
Its input views receive an abstract shared access environment with externally
supplied backing, not secretly invented ownership of external memory. The
proof must work for any caller satisfying that environment. It cannot close
an external scope or recover its lender's resource. Equal/overlapping view
arguments remain valid instantiations; distinct binder names are not a
separation premise.

Use one hidden callee access scope for the input-view environment. Each
view clause selects a description in it; several descriptions can use the
same available access capability in one sequential context. Never mint a
separate full live token for each formal parameter and later identify those
tokens when the actual pointers alias.

The caller constructs this environment with backing entries of two kinds:
newly lent owned pieces, and shared reborrows of existing loans. A shared
reborrow pins a selected parent access share as a dependency of the fresh
call scope. Several clauses using the same parent capability share that
dependency; different parent scopes remain separately recorded. The callee
gets access to the fresh scope, while the caller retains its close right.
Closing that scope returns the pinned parent shares and enables recovery
only for newly lent owned pieces. It never closes the parent scopes.

This is the default calling convention, including nested readers. It makes
generic function certification independent of whether its caller supplied
owners, one outer loan, or several outer loans. Projected child backing is
checked at creation against the parent's frozen footprint and generation.
Read checks use the child record directly; closure obligations maintain the
parent protection without walking the full ancestor chain at every load.

Prepare calls in a checked two-phase operation:

1. Instantiate the interface and evaluate addresses, bounds, model arguments,
   and dependent loads in the prescribed entry snapshot. Record the actual
   support for every such load.
2. Plan the required owned transfers, consumes, and shared loans jointly.
   Check coverage, resource quantities, cross-clause conflicts, and any
   explicitly proved conditional partition. A preliminary read during
   planning does not lend or duplicate the resource.
3. Check the complete plan and atomically publish the caller residual,
   suspended escrow, callee capabilities, scope bindings, and frame evidence.
   Keep the plan separate from authority until its obligations are discharged.
4. Execute/apply the callee rule. Its write/havoc footprint comes from the
   checked transferred authority. Reentrant calls see only authority their
   own contracts actually supply; saved caller owners do not become usable.
5. At each returning path, check returned owned/consumed/produced resources,
   restore callee-held access shares, close scopes created for this call,
   recover their escrows, and check packaging/postcondition transport.

The exact ordering of postcondition evaluation must respect the current
entry/post metadata: callee postconditions are checked before dropping access
needed to interpret them; only justified facts are transported to the caller.
Validate all return obligations before committing caller recovery. A failed
callee result cannot leave a recovered owner beside live access.

When satisfying a view from an existing view, split/hold access from its
existing backing under the child dependency and return it when the child
scope closes. A fresh child scope is justified by that held parent authority;
it is not a new independent source of memory access. Keep the dependency
graph acyclic by construction. Directly forwarding the same scope can be a
later checked optimization, but is not required and must preserve the same
call extent, interface interpretation, and return obligations.

The roles in the normalized resource specification remain distinct:

| Interface item | Boundary treatment |
| --- | --- |
| Borrowed ownership (`owns`) | Move usable ownership into callee, return the promised resource on return; this is not a shared loan. |
| Borrowed view (`views`) | Lend from ownership or pass existing scoped read authority; no independent owner remains usable. |
| Consumed resource | Transfer the selected resource with no automatic recovery promise. |
| Produced resource | Require checked output authority and composition with the caller frame; cannot mint a live access share. |
| View in an output or packaged output | Preserve an explicitly existing outer dependency, or reject an escaping loan that the supported interface cannot express. |

Do not interpret every ensured `View` as a new persistent capability.
Implicit return of a call's own input view normally gives back the access
share and closes the call-created loan. Conversely, blanket deduplication
against a caller owner is no longer a valid way to discharge obligations.
Before accepting any explicit view-producing form, classify where its live
authority comes from. Unsupported escaping-borrow contracts get a source
diagnostic; merely rejecting a valid returned raw C pointer is incorrect.

### D9. Callbacks, refinement, effects, and non-return

Direct verified calls, named function contracts, indirect callbacks, explicit
execution theorems, automatic contract formation, and certification must
share the same transition boundary. A named contract's body-independent
interface cannot assume hidden resource availability from its original
concrete function.

Refinement must account for resource transformations, not just compare
`Own` and `View` variants. An implementation verified with a view can serve
an interface that gives ownership if a checked adapter lends and recovers it.
An implementation that requires a writer cannot serve an interface offering
only a stable view. Check callback execution and refinement on concrete live
callers; a proof under an inconsistent precondition is not a bad-call test.

The exact function-pointer `Contract(p)` evidence retains its supporting
table cell/resource generation. An active view of that supporting cell
prevents mutation; an ordinary owner-supported observation is invalidated by
an allowed mutation. Stable views must not accidentally make all callback
facts permanent. Preserve the real rbtree callback footprint regressions.

Memory-effect summaries are consequences of the transferred authority.
They cannot widen it. Audit direct stores, abstract call havoc, loop havoc,
allocation effects, and trusted external contracts. External specifications
remain explicit trust assumptions, but their declared effects must still
compose with the caller's loans. An unknown implementation is not permission
to ignore a frozen range.

Every normal and early return uses the same discharge rules. A non-returning
path does not synthesize a returning owner; a partial-correctness proof may
retain an unclosed loan on that path without pretending recovery occurred.
Keep termination proof obligations separate. Unsupported exceptional exits,
longjmp, and future C++ unwinding need explicit lifetime transitions later;
do not assume cleanup occurred because a source block or proof task ended.

### D10. Stack storage, heap storage, and object lifetime

The current caller-local view shortcut must become checked lending from
implicit local authority. Ordinary C users still need no resource clause
for each local array. Materialize or identify the local's authority internally,
tie it to the local allocation generation, and suspend the selected bytes
when lent. Direct local assignment, indirect aliases, initializer paths,
aggregate writes, and loop/call havoc must consult the same suspension state.

Do not implement this solely by denying external stores. A local's block
prefix is not evidence that the current component may write it. Likewise,
free checking only for visible `View` entries misses descriptions stored
inside resources or held by another context. Allocation lifetime checks must
use active loan/backing evidence, including loans of subranges.

For heap operations retain the existing allocation token, size, initialized
state, and pointer checks. A live subrange loan prevents free and any realloc
operation capable of invalidating that allocation, even if the allocator
might fail or return the same address. After scope closure/recovery, the
existing legal operations succeed. A recycled address has a fresh allocation
identity and cannot revive an old descriptor. Ending access also does not
allow a later recovery to resurrect an already-ended object: destruction
must discharge or explicitly consume pending escrow/restoration obligations,
and recovery checks the still-valid allocation generation. Ordinary P1
call return recovers before local lifetime teardown.

Owning raw storage and viewing it does not certify a typed initialized value.
Keep existing initialization checks at reads; P1 is not adding Rust's typed
validity rules. Globals, static storage, and literal storage retain their
existing lifetime and mutability classifications while using the same access
checks where applicable. A compiler-certified immutable literal may have
permanent read support; it is not a general way to give mutable memory an
unbounded loan.

### D11. Loops, proof branches, and hidden dependencies

An outer function's input view stays active through its loops. A loop that
narrows the body to read access over surrounding ownership needs either
an owner-supported read projection constrained by the body's checked effects,
or an actual scoped loan if it transfers independent read access. It cannot
create a stable view and retain a usable overlapping writer in the body.
Audit `loop_body_resource_context`'s current automatic viewed forms.

Initially scope new temporary loans inside one iteration/call and close them
before the backedge. Outer loans may cross the loop if the invariant carries
their exact authority/dependencies. The backedge must preserve that state;
the invariant cannot existentially forget a leaked share and recreate a full
one on the next iteration. More general changing loan populations require
an explicit conservation invariant and are outside implicit inference.

Treat proof branch cloning as alternatives. Each returning branch must
discharge its own scopes or present compatible surviving obligations.
If one branch ends an outer loan and another retains it, do not union their
resources or unconditionally choose the recovered owner. Keep separate
continuations where needed, or require a checked reconciliation before the
join. Ended branch-local scopes can disappear after proper discharge.

The same rules apply to hidden obligations in folded resources, opened
populations, instance-field scopes, witnesses, and pending proof rewrites.
Resource equality at a join includes the relevant capability/dependency
delta, not only the visible `owns`/`views` list. Use persistent ancestry
and changed-entry indexes; a join must not rewalk the full proof history.

### D12. Sharing families and later Rust interpretation

Ordinary structural resources can share their checked stable body. Their
owned memory becomes borrowed memory under the same protection; observing
them must not reveal owned children. Abstract token lending suspends the
selected token's consumption while the view is active. Other counted units
may remain available. A field-bearing exclusive instance remains unviewable
unless a separately checked sharing interpretation is introduced.

For counted composites, preserve the existing distinction between population
quantity and its population-wide body. Lending a unit must not instantiate
a second independently owned body. A view of that body keeps its actual
memory and resource-state dependencies stable. If consuming another unit
would change a fact advertised by the borrowed body, that transition needs
an appropriate protocol or must wait for the borrow to end. The simple
bodyless-token case may keep its remaining units usable; do not generalize
that behavior to every population invariant. Track pure-looking facts that
depend on resource counts/generations as carefully as memory-dependent facts.

Keep a family sharing operation distinct from a persistent core operation.
Some abstract families may expose facts that remain true through mutation.
That does not make their protected payload an ordinary stable memory view.
Unsupported sharing fails explicitly; never recursively expose arbitrary
owned bytes just because a handle is copyable.

The concurrency model's mutex has a stable shared protocol handle, an
invariant owning its payload while unlocked, and one exclusive guard after
acquisition. Release returns the payload and invariant facts. No raw payload
view follows from the handle. The model's thread-local mutable cell allows
its chosen sequential protocol but refuses transfer to another context.
This is a check of abstraction boundaries, not a production mutex/Cell API.

The Rust correspondence remains deliberately partial. Shared references
require more than pointer constness; exclusive reborrows also restrict
conflicting parent reads and require access-origin reasoning. Rust's
`UnsafeCell` permits a particular interior-mutation interpretation without
removing the need to prevent data races. Rust's exact unsafe alias rules are
not a settled complete model. See the
[Rust Reference](https://doc.rust-lang.org/reference/behavior-considered-undefined.html)
and [UnsafeCell documentation](https://doc.rust-lang.org/std/cell/struct.UnsafeCell.html).
Do not impose these source-language alias constraints on ordinary C pointers.

For model-only exclusive reborrowing, move parent usable authority into a
child and suspend conflicting parent access. A shared child permits shared
reads, while an exclusive child excludes conflicting parent reads and writes.
End the child with its returned authority before enabling the parent. For a
returned field loan, preserve the parent recovery dependency across function
return and recover the field's updated state, not a saved pre-mutation value.
Scope inclusion, access provenance, C storage lifetime, and language reference
validity are separate relationships; a single lexical stack cannot represent
all of them.

### D13. Certificates, diagnostics, and complexity

Add kernel-checked loan transitions to the existing proof object/evidence
path. Evidence must establish the actual predecessor's available capabilities,
the resource selection and side conditions, the exact consumed/produced
delta, and the successor. A surface-supplied after-state, resource hash, or
fresh-looking integer is not sufficient. All normal proof paths must check
the same rules.

Keep access checks and transition checking deterministic. Smart tactics may
find a partition or restoration proof, but the expanded simple proof must
name enough evidence to check it with bounded local work. Ordinary call
syntax may keep compiler-inserted scope mechanics implicit if the call's
checked certificate records them and audit exposes the relationship.

Examples of required diagnostic content, not exact output spelling:

- A store conflicts with the view of `node->next` lent to `inspect`;
  name the loan origin and the attempted write range.
- Call clause 2 requires ownership overlapping the stable view in clause 1;
  report proven overlap or the unresolved separation obligation.
- Scope closure is missing a particular access share or open-resource
  obligation; point to the call/open that retained it.
- A descriptor belongs to an ended scope, or recovery has already consumed
  the entitlement; name the original loan.
- An output tries to retain a loan past the supported call boundary; explain
  the missing lifetime relationship, without silently upgrading permissions.

Use existing bounded diagnostics, structured refusal categories, source maps,
and provenance. Do not print every loan, memory snapshot, or resource in the
project. For unknown aliasing say that separation is unproved; do not report
a known data race.

Index active shares/loans/support by semantic ID, memory by allocation/range,
and reverse dependencies by their immediate parent. Persistent cloning is
constant/logarithmic; a fixed read, split, join, or single-loan recovery
does not visit unrelated entries. Do not add per-store scans of all loans,
eager pairwise reader/writer constraints, or complete-state hash keys.
Reuse the current range evidence/indexing, improving affected fallbacks
when necessary rather than claiming they are already scalable.

Retain checked local proof evidence when symbolic overlap needs explicit
reasoning. The simple checker verifies named coverage/separation witnesses;
it does not search the entire resource context for a favorable partition.
Closing many explicit loans or folding many declared body members may cost
their output size. Repeated fixed-size calls must not accumulate a historical
scan through dead loans. Instrument token-tree bookkeeping as well as memory
and resource operations.

The four-size scaling gates below implement the existing
[verification efficiency contract](../docs/internals/verification-efficiency.md).
Tests must count the work being protected: moving an uncounted scan outside
an instrumented closure is not an optimization.

### D14. Worked traces for implementers

These traces are design notation. They pin the meaning of the hidden call
operations without introducing Surface Click syntax.

**One reader followed by mutation.** The caller starts with Own(x), allocation
generation g, and value 0. It begins k, retains Close(k), and lends Own(x)
into escrow e. The callee receives View(k, e, x) and the root access
capability. The caller's saved frame has Recover(e), but no usable Own(x).
The callee reads 0 and returns the root. The checked return validates its
guarantees, closes k, consumes Recover(e), and reinstalls Own(x). The caller
can now store 1. The scalar result 0 remains valid; a retained description
cannot load x through k, and its old value fact cannot assert that current
x is still 0.

**Two aliased view parameters and a nested reader.** A caller owning x calls
read_twice(p, q) with p == q == &x. One escrow backs two descriptions; the
callee need not own two shares merely to read through two aliases in its
single sequential context. To invoke a nested reader it splits its access
leaf, pins one child under a fresh nested call scope, and retains the other.
The nested reader uses that new scope's description and access. Its return
closes the nested scope and releases the pinned parent child; exact sibling
join restores the outer leaf. The outer return gives the caller its root.
A parallel version would require the
explicit two-context partition that R27 models, not cloning this state.

**Folded cell, viewed link, mutable value.** The caller owns cell(n), whose
body owns n->next and n->value. It wants a setter with views n->next and owns
n->value. The plan checks the body and field separation, suspends independent
use of the parent head, lends the next field, and transfers value ownership.
The setter may write value but not next. Return recovers next and receives
the updated value field. Refolding cell checks the resulting body's facts;
if a model index records the value, its post-call index must be updated by
the contract/proof. The pre-call parent cannot silently retain an obsolete
value fact.

**Borrowed fact hidden in a resource.** A reader has View(k, x), one access
leaf, and evidence that x == 0. It folds a scoped zero-cell resource. Folding
captures the dependency bundle; it does not manufacture an unscoped timeless
assertion. Opening that bundle re-exposes only borrowed access with the same
dependency. Scope end cannot discard the bundle's live access obligation.
Unfolding/closing and returning its share allows normal recovery. A copied
old snapshot proposition may remain, but no current-memory promise escapes.

**Loan ending on only one branch.** Both alternatives start from the same
caller resource state. The true branch can return all of its access and
recover; the false branch can retain its share. These are alternative
states, not pieces to add together. A common continuation cannot receive
unconditional ownership unless both alternatives prove it. If the false
branch first returns its access and recovers too, the checked join can
reconcile the owned result without merging historical scope identities.

## Regression catalogue

The IDs below are stable handoff names. They describe new paired tests to
write, not tests claimed to exist today. Keep current positive fixtures as
inputs. Add a rejecting case that reaches the intended authority check;
an earlier parser error, missing allocation, or unrelated proof failure is
not coverage. Use real allocated live callers for overlap/free negatives.
Prefer explicit simple proofs for the semantic core.

| ID | Positive witness | Required rejection or preservation check | Minimum layer |
| --- | --- | --- | --- |
| R01 | Lend one initialized cell, read it, close, recover, write | Same-value write while access is active fails | Kernel and C call |
| R02 | Two readers share one backing and return both shares | Close/recover with one missing share fails | Kernel/model |
| R03 | Split a leaf, return exact siblings, join | Duplicate leaf, wrong sibling, wrong scope, and ancestor/descendant compositions fail | Kernel |
| R04 | Copy descriptors freely during a loan | Old descriptor fails after end and after another scope starts | Kernel |
| R05 | Recovery once restores the selected ownership | Double recovery and recovery from only an old composition premise fail | Kernel/certificate |
| R06 | Two aliased read parameters and nested readers verify | Reader cannot return outer authority as a new owner | C and kernel |
| R07 | Owned alias probe reads and writes through equal pointers | A concrete caller cannot supply overlapping independent owned/viewed clauses | C |
| R08 | View one field/subrange and mutate the disjoint remainder | Bytewise overlap, even with different element widths, fails | C/kernel |
| R09 | Read-call on a heap object, then free | Free/realloc of a live allocation while any nonempty subrange is lent fails | C/kernel |
| R10 | Call a reader of a local array with no explicit local clause | Direct local/alias store, initializer overwrite, or lifetime end bypassing suspension fails | C/kernel |
| R11 | View a pointer cell and separately authorize a pointee | Pointer-cell view alone cannot authorize pointee access; entry-selected footprint does not retarget | C/kernel |
| R12 | Preserve a snapshot fact, recover, then write a different value | Old fact cannot become a current load/value claim or restore an access token | C/certificate |
| R13 | Observe an owned composite, unfold, legally mutate, refold | Observation does not permanently freeze the owner; old supported facts invalidate | C/kernel |
| R14 | Read through a viewed nested composite | Open/unfold cannot expose write ownership or drop the loan dependency | C/kernel |
| R15 | Fold a resource whose fact is covered by a stable view | Missing access, uncovered read, false fact, and hidden escaping lifetime fail | C/kernel |
| R16 | Open and close a borrowed body with access retained | End scope while body/opening is outstanding fails | Kernel and resource proof |
| R17 | Loan a selected token unit, recover, consume it | Consume lent unit or duplicate its quantity while lent fails; other units remain usable | Kernel/C |
| R18 | Direct, named, indirect, execution-theorem, and certification routes agree | Missing loan obligation or view-to-writer refinement fails on every route | C/kernel |
| R19 | View-based implementation serves an owned interface via a checked loan adapter | Owned implementation cannot satisfy view-only interface | Contract refinement |
| R20 | Reentrant callback reads a lent cell | Callback/hidden-state write to the cell fails; disjoint callback mutation succeeds | C |
| R21 | Stable viewed table cell supports callback evidence | Allowed mutation of owner-supported table cell invalidates old callback evidence | C |
| R22 | Both branches finish their own loans and recover | One-sided closure cannot produce unconditional ownership after join | Kernel/C |
| R23 | Loop retains an outer view and closes per-iteration reader calls | Backedge cannot discard a live share or regenerate a full root; loop havoc cannot write frozen bytes | C/kernel |
| R24 | Early return discharges call-created loans | Return cannot recover caller-owned field while a returned model loan remains live | C/model |
| R25 | Caller result/sidecar proof survives supported packaging changes | Equal resource term after consume/recreate does not revive old support generation | Kernel/resource proof |
| R26 | Ordinary verifier, expand/reverify, profile, and audit agree | Tampered loan ID, range, predecessor, share, scope-end, and recovery evidence fail kernel checking | Certificate/engine |
| R27 | Contexts own disjoint ranges and each writes its range | A reader in one context excludes an overlapping writer/free in the other | Model with kernel-mapped rules |
| R28 | Exclusive parent lends shared child, then exclusive child, and recovers | Conflicting parent writes fail for shared child; parent reads/writes fail for exclusive child | Model |
| R29 | Returned child loan updates caller field and ends later | Parent recovery waits for child and restores updated field state | Model |
| R30 | Mutex handles acquire/release one guard; local cell works within its home context | Unguarded payload access, duplicate guards, and cross-context local-cell transfer fail | Model |
| R31 | Empty view grants no bytes; initialized ordinary read succeeds | Empty view cannot load or prove nonnull; uninitialized read remains rejected | Kernel/C |
| R32 | All share/loan operations remain local with unrelated frame state | Four-size deterministic curves expose ambient scans, history growth, and deep token arithmetic | Kernel/surface scaling |

Start from these existing files rather than inventing a new proof vocabulary:

- R06/R07: [alias-owned.click](../design/borrow-probes/alias-owned.click),
  [alias.c](../design/borrow-probes/alias.c), and
  [alias_and_cleanup.cpp](../design/borrow-probes/alias_and_cleanup.cpp).
  The C++ file is compiler/model evidence only in this issue.
- R08/R13: [field-split.click](../design/borrow-probes/field-split.click) and
  [composite_piece_caller_frames_viewed_field.md](../mdtests/composite_piece_caller_frames_viewed_field.md).
  The latter's existing overlapping contract needs a sidecar migration.
- R09: [heap_scoped_borrow_then_free.md](../mdtests/heap_scoped_borrow_then_free.md).
  The existing [heap_free_rejects_borrowed_access.md](../mdtests/heap_free_rejects_borrowed_access.md)
  rejects missing live-allocation evidence; it does not by itself test
  free with a valid allocation token and a still-live loan.
- R10/R31: [borrowed_local_view_in_bounds.md](../mdtests/borrowed_local_view_in_bounds.md)
  and [borrowed_local_view_bounds_rejected.md](../mdtests/borrowed_local_view_bounds_rejected.md).
- R18/R21: [rb_augment_callbacks_helper_owns.md](../mdtests/rb_augment_callbacks_helper_owns.md),
  [rb_augment_callbacks_helper_owns_rejects_unseparated.md](../mdtests/rb_augment_callbacks_helper_owns_rejects_unseparated.md),
  and [opaque_call_does_not_preserve_overlapping_field.md](../mdtests/opaque_call_does_not_preserve_overlapping_field.md).

For R32, vary sizes 16, 32, 64, and 128 independently for live loans,
unrelated resources, completed sequential loans, reader nesting, and
split-tree depth. Add a selected folded resource with increasing unrelated
definitions. Separate construction cost, operation cost, and total repeated
workflow cost. The fixed operation should be independent of unrelated
entries except indexing; explicit n-operation workflows should follow the
documented near-linear bound. Compare counted work against those bounds,
not a large fixed threshold chosen after looking at timings. Include a
validity check so an early failure cannot masquerade as good scaling.

## Implementation overview

The three themes below summarize the change; the V0-V19 cards afterward are
the assignable units. Start with the model and reviewed rules, then implement
the shared authority/certificate boundary, then connect execution paths and
migrate contracts. A model result alone does not complete this issue; the
stable semantics must land in Click.

### 1. Separate supported observations from outstanding borrows

Keep `CResourceSpec`'s access, role, and snapshot fields. Add semantic identities
for loans and their scopes, with loan mode, selected resource/footprint,
support generation, parent dependencies, and a recovery obligation. Avoid
equating scope identity with a lexical block or baking in a single lexical
stack as the only possible lifetime relationship. Lifetime access
shares must participate in resource transfer, branch joins, and certificate
checking. These can be kernel resources or indexed state with checked deltas;
they cannot be advisory surface metadata.

Stop using an owner-derived `CResourceFact::View` as if it were an independently
held borrow. Owners can answer read-authority queries directly. Supported
observations should name the owner/loan they depend on and retain current
snapshot invalidation rules. `observe` of an owned composite must not create a
new outstanding borrow merely to read its facts. Observation of a genuine
borrowed composite must retain that borrow's scope on all projections.

Audit `core`, entailment, consumption, normalization, supported expansion,
fold/unfold/open/close, and return-view deduplication together. For mutable
memory, do not retain `core(Own(R)) = independently usable View(R)`. A family
may still have a persistent core for facts that really survive its updates;
not every resource family must use the same core law.

### 2. Make contracts perform real scoped lending

Change the shared call-transfer engine, covering direct calls, named contracts,
callbacks, and contract refinement. Satisfying a view from ownership suspends
the selected ownership in loan storage; satisfying it from an existing view
uses that loan or a checked shorter reborrow. Nested readers may alias.

Evaluate all required resources jointly. A contract with an owned part and a
viewed part requires a valid partition; unknown aliasing is not evidence of
disjointness. Preserve range splitting and the untouched owned remainder.
Recover only the input loans that actually end at return. Default input views
last for the entire call, not merely until the callee's last load. Reentrant
callbacks and hidden state must respect the outstanding loans too.

Check stores and abstract call/loop effects against usable ownership. Route
stack/heap/global storage through the same loan restrictions while preserving
their existing lifetime and allocation distinctions. A body-independent call
cannot havoc frozen memory just because an old owned footprint includes it.

Keep the initial public contract language scoped to borrows it can represent.
A returned C pointer is not automatically a Rust reference or a returned
loan. Before supporting escaping resource borrows, add explicit scope binding
in contracts and check that the lender cannot recover at ordinary call return.
Early returns must discharge the same obligations; never recover solely because
a local variable disappeared or a destructor is expected to run.

### 3. Migrate C contracts and stable resource facts

- Keep existing C unchanged. Aliased read/write code can use ownership of the
  shared location, as `alias-owned.click` demonstrates. General possibly
  overlapping source/destination ranges may need a permission partition or
  conditional contract; do not impose false disjointness on valid C inputs.
- Replace `views whole; owns field` with appropriate views of the unchanged
  portion, or ownership of the whole plus a precise postcondition. Do not
  automatically upgrade every view to ownership: that loses legitimate
  overlapping-reader callers and may weaken framing precision.
- Keep ordinary read-helper calls, recursive readers, viewed loop ranges,
  folded resources, and subsequent owner mutation/free concise. Include real
  callback footprints from the rbtree work in the migration audit.
- Permit a composite fact such as `fact p[0] == 0` to depend on an active
  stable view once its lifetime/support is tracked through the composite.
  Update the current owned-memory-only coverage rule in
  `src/surface/validation/definition_validation.rs` together with kernel
  observation/framing checks. Folding must not hide an expiring borrow or
  turn a scoped fact into a timeless current-memory assertion.

## Implementation chunks and dependency order

### Assignment and integration contract

Assign one card at a time to a Luna agent. Each task prompt should contain:
the integrated starting commit, this file and its D/R sections, the selected
card, its predecessor handoffs, the file ownership boundary, and the shared
completion checklist below. The agent should not have to reconstruct intent
from this conversation. Do not assign a card until its dependencies have
landed and their APIs/tests exist.

The table gives a recommended default order. Some adapters can be developed
independently after the common API is fixed, but most touch shared kernel
files. Start sequentially. Parallel assignments require disjoint file
ownership established by the coordinator; the table is not permission for
several agents to edit `functions.rs` or `resource_algebra.rs` at once.

| Card | Deliverable | Depends on |
| --- | --- | --- |
| V0 | Fresh baseline, fixture classification, authority-path inventory | None |
| V1 | Small transition model, preservation arguments, reviewed API contract | V0 |
| V2 | Scope identities, conserved share tree, persistent ledger | V1 |
| V3 | Memory/token lending, escrow, projection, and recovery | V2 |
| V4 | Kernel proof transitions and hostile certificate tests | V3 |
| V5 | Owner-supported observations separated from borrowed access | V4 |
| V6 | Joint checked call-resource planner | V5 |
| V7 | Direct-call input/return binding and scoped recovery | V6 |
| V8 | Named contracts, callbacks, and refinement integration | V7 |
| V9 | Implicit local authority and heap/lifetime enforcement | V7 |
| V10 | Loop invariants, effects, branches, and early returns | V8, V9 |
| V11 | Composite/population opening and dependency preservation | V5, V7, V10 |
| V12 | Stable viewed facts and guarded coverage | V11 |
| V13 | Small C contract migrations and explicit-view outputs audit | V8, V9, V12 |
| V14 | Model checks for threads, mutable reborrows, and protocols | V4, V11 |
| V15 | Expansion, audit, refusal diagnostics, and import/proof identity | V8, V10, V12 |
| V16 | Deterministic complexity gates and local fixes | V10, V11, V15 |
| V17 | Full corpus/rbtree contract migration and compatibility record | V13, V15, V16 |
| V18 | Independent adversarial review and production-readiness gate | V14, V17 |
| V19 | Default semantics cutover, documentation, final cleanup | V18 |

Common completion checklist for every implementation card:

1. Work in an isolated task branch/worktree from the assigned integrated
   base. Read applicable AGENTS instructions and the current predecessor
   handoff. Inspect symbols before assuming the planning map still matches.
2. Implement only the card's boundary. Add meaningful paired positive and
   negative tests and the deterministic work checks relevant to new hot
   paths. Preserve original C bytes in existing fixtures and examples.
3. Use the shared bounded verification engine. A prompt ordinary proof
   failure may be repaired with appropriate proof steps; tooling slowdown,
   unverifiable expansion, or unusable diagnostics must be reduced and fixed
   before proceeding. Do not increase limits or quarantine coverage.
4. Run focused tests, then the unfiltered `scripts/check.sh` and judge its
   exit status. Do not commit a failing placeholder test or merge an
   incomplete prototype. Report a blocker and a small intended regression
   if it cannot be resolved inside the card; do not create another issue
   without user authorization.
5. Leave a concise handoff in the task result: commit/base, exact APIs and
   invariants added, R IDs covered, test commands and exit statuses, whether
   production behavior changed, remaining limitations, and anything the next
   card must use or must not rely on.
6. The coordinator checks the diff, coherent scope, primary cleanliness/base,
   and relevant/full gates before Git integration. If the base moved, rebase
   and rerun affected checks. Downstream work starts from that tested commit.

Focused command patterns, with filters chosen for the card's actual tests:

    cargo nextest run --lib resource_tests
    MDTEST_FILTER=borrowed_local_view cargo nextest run --test mdtests --no-capture
    scripts/check.sh

These focused commands are examples, not substitutes for the gate. If new
modules/test names differ, report the real filters. Record the verifier
process tree as exited after an interrupted or timed-out run before trusting
subsequent timings.

Use this future assignment template after implementation is authorized:

    Implement card V__ of issues/fix-views.md from integrated commit ____.
    Read design sections D__ and regressions R__ plus predecessor handoff ____.
    Your file boundary is ____. The common API is the one in commit ____.
    Preserve existing C source. Do not implement successor cards or redesign
    the loan protocol. Complete the card's tests and scripts/check.sh.
    Return a tested commit and the handoff below; report any concrete blocker.

Handoff template:

    Card and base:
    Commit:
    Production behavior changed? If so, exactly how:
    Checked APIs / invariants added:
    R IDs -> actual test names and verification layer:
    Commands -> exit statuses:
    Scaling evidence, if applicable:
    Temporary adapters and required removal:
    Remaining limitations / next card inputs:

If a card reveals more than one independent architectural change, its agent
should return a proposed smaller boundary before expanding scope. The
coordinator can split the card into named subtasks in this same issue with
the same laws/regression IDs. A Luna task should finish one reviewable
transition or integration boundary, not silently become the entire refactor.

### Staging without an unsafe partial cutover

V2-V4 can land checked APIs and kernel tests without changing how ordinary
source contracts are interpreted. V5-V17 then route proposed stable-view
inputs through the same checked engine in focused tests, while existing
contracts are migrated. Any state containing a real loan must obey all of
its access rules; an adapter may not silently fall back to old view behavior
for an unsupported operation.

If a temporary input-interpretation selector is needed, keep it internal to
tests and the coordinated rollout, with explicit semantic identity. It may
choose how entry contracts are instantiated; it must not skip checking or
select a second verifier. Scope-bearing states and certificates cannot be
consumed by an old rule that ignores their obligations. Never cache or
certify an old-interpretation result as a stable-view result.

Keep the existing public behavior unchanged until the complete path and
corpus are ready, and keep this issue open. The candidate path must cover
ordinary verify/expand/profile/audit, not a hidden stand-alone checker.
V18 requires the full corpus under the candidate interpretation with no
uncovered fallback. V19 enables it by default and removes temporary selectors,
legacy independent-memory-view construction, and obsolete tests/docs.
No permanent dual semantics or public compatibility switch is part of P1.

At V1, pin the precise staging seam and removal list using the actual engine
APIs. If isolating the candidate interpretation would require a second
checker or broad pervasive flags, stop that approach: keep the dependent
adapter changes in a coordinated integration worktree and integrate one
coherent tested cutover commit. Do not make a Luna agent invent a migration
architecture mid-card or merge a half-enforced semantic change to stay green.

### V0 — Baseline and classify existing usage

**Read:** decision, D1-D2, catalogue; resource docs, the current
`memory-vs-resources.md` handoffs, and the named positive fixtures.

**Boundary:** investigation and existing-test execution only. No semantic
changes or new user-facing issues. Record results in a dated handoff section
of this file when this future card is actually assigned.

**Work:**

- Record the base and unfiltered gate verdict. Re-run the two migration
  probes through ordinary verification. Classify weak-view fixtures without
  claiming they already exercise loans.
- Inventory `views` declarations in mdtests, examples, stdlib/contracts,
  and proof-body resource definitions. Classify: pure readers; owner-only
  observations; overlapping owner/view; partial field/range; explicit output
  view; nested/folded/count/instance; local/heap/global; callback/loop.
- Name each path that creates, normalizes, returns, or uses a view. Include
  `access_mode_core`, consumption, return deduplication, initial projection,
  loop viewed forms, stack shortcuts, and proof resource rewrites.
- Record which existing memory/resource unification changes are already
  integrated. Map their transition/support API to D3; do not redo W1 or
  revive removed variants. Identify fixture expectations that change and
  the exact positive replacement for each.

**Done when:** the coordinator has a concrete migration inventory, current
symbol map, baseline verdict, and a list of entry-point consumers to check
off in V18. R07/R08/R09/R10 existing witnesses are classified with actual
outcomes. A search count alone is not the inventory.

### V1 — Model the laws and freeze the common API

**Read:** D1-D6 and D12; R01-R05, R27-R30. **Depends on:** V0.

**Boundary:** a small test/model module and design handoff. A proposed home
is `src/kernel/tests/loan_model_tests.rs`; choose module wiring consistent
with the current tree. This module is not a production threading engine.

**Work:**

- Define the small state machine: byte cells with allocation generation,
  owners, loan escrow, view descriptions, binary shares, close/recovery
  rights, and two independently held context fragments.
- Implement the transition rules and invariant predicate. Include a naive
  owner-plus-independent-view transition as an explicitly invalid comparison
  whose counterexample the test detects, not an expected-success verifier.
- Handwrite the two-reader trace and adversarial R01-R05 cases. Enumerate
  bounded reachable small states with a fixed deterministic bound, recording
  the bound and explored operations. Check compatible-frame preservation and
  distinguish branch cloning from context splitting.
- Write the inductive preservation argument for each operation, including
  registration, discarded shares, open bodies, and recovery. The invariant
  should explain why another context cannot regain a writer between reads.
- Set the common API signature sketch, error categories, identity ownership,
  staging seam, and exact projection semantics for later cards. Reserve the
  parent-dependency seam used by V14 without promising unsafe Rust support.

**Done when:** model tests and hand arguments agree; no closure is based
solely on descriptor counts; the coordinator reviews D2-D6 against the
counterexamples. Record decisions in this file before V2 starts. If the
model contradicts this proposal, resolve the design first rather than
asking later agents to choose competing rules.

### V2 — Implement scope and access capability storage

**Read:** D3-D5, D13; V1 API handoff. **Depends on:** V1.

**Boundary:** resource/state types and a narrow loan-state module, plus unit
tests. Likely integration points are `src/kernel/primitives.rs`,
`src/kernel/primitives/resource_algebra.rs`, and
`src/kernel/primitives/memory_state.rs`. Splitting out a module is encouraged
if it keeps the public checked boundary narrow; do not rename unrelated APIs.

**Work:**

- Add fresh semantic IDs, persistent ledger roots, split-node records,
  active-leaf ownership, close rights, and indexed direct dependencies.
- Implement begin/split/join/end mechanics with private validated creation.
  Keep end unavailable when obligations exist; no memory-lending API yet.
- Include the state in identity, substitution/transport where applicable,
  and branch ancestry without cloning complete maps or building deep keys.
- Distinguish host-language data sharing from logical capability ownership.
  Expose no public unchecked constructor that can mint a root or leaf.

**Tests:** R02-R04, duplicate/forked token composition, fresh IDs in sibling
branches; a four-size split-depth and unrelated-scope lookup test.

**Done when:** capabilities are conserved by every available operation,
constant-size tree nodes avoid repeated-halving arithmetic growth, and old
source behavior remains unchanged. V3 receives checked IDs/handles rather
than raw maps it can edit.

### V3 — Implement lending, escrow, and recovery

**Read:** D2-D6, D12; V2 handoff. **Depends on:** V2.

**Boundary:** checked loan/resource operations and family algebra tests;
no Surface Click or C-call wiring.

**Work:**

- Add atomic lending from owned memory, checked subrange selection and
  residuals, description projection, active read authorization, and recovery.
  Prevent escrow from satisfying ordinary write/read-owner queries.
- Support several descriptions of one backing and compatible overlapping
  readers. Freeze byte ranges and allocation identity at entry.
- Add shared child reborrowing backed by pinned parent access. Check
  coverage once, retain immediate dependency indexes, release parent access
  on child closure, and reject cycles or ending a parent prematurely.
- Handle selected token-unit suspension and recovery while preserving
  remaining quantity; retain rejection of unsupported instance views.
- Define normalization that preserves loan/support identity and obligations.
  Eliminate no loan by owner/view absorption in the new interpretation.
- Record and check restoration recipes for the simple pieces this card
  supports. Complex composite reassembly belongs to V11.

**Tests:** R01-R09 at kernel-operation level, R11/R17/R31, differing byte
widths, unknown separation, failed-operation rollback, and recovery after
disjoint writes. Include four-size single-loan lookup with unrelated owners.

**Done when:** a kernel client can execute the basic two-reader trace and
cannot recover through normalization, an old fact, or a still-live share.
Unsupported symbolic partitions return explicit obligations/refusals.

### V4 — Make every loan operation a checked proof transition

**Read:** D2, D5, D13. **Depends on:** V3.

**Boundary:** `src/kernel/proof/execution.rs`, proof object integration, and
kernel proof tests; narrow supporting APIs only.

**Work:**

- Add evidence types and checked proof-object operations for the V2/V3
  transition family. Bind their inputs to the current execution state.
- Carry capability/support deltas through resource rewrites and outcome
  checks. A supplied post-state alone must not certify the operation.
- Make capabilities unavailable to pure theorem duplication/rewrite rules.
  Check that retaining a historical composition is harmless.
- Add hostile-certificate tests by deliberately changing each semantic input
  while preserving superficially equal resource terms.

**Tests:** R05/R12/R26, forged predecessor, duplicate recovery, swapped range,
stale allocation generation, wrong-scope leaf, and unsupported after-state.

**Done when:** independent kernel checking rejects each mutation and normal
evidence advances the existing proof object. V5-V12 can only propose a
transition, never manufacture accepted loan authority in surface code.

### V5 — Separate owner observations from independent views

**Read:** D3, D7, D13. **Depends on:** V4.

**Boundary:** core/support operations in `resource_algebra.rs`, observation
validation in `kernel/proof/execution.rs`, and the minimum matching paths in
`src/surface/proof/resources.rs`.

**Work:**

- Let ownership satisfy direct read-authority queries without creating loans.
  Represent owner-supported projections with occurrence/generation support.
- Preserve support through observation, cached body expansions, and compact
  composition facts. Distinguish an explicit scoped view from a projection.
- Route transfer requests using such a projection back to its owner/loan;
  an observation cannot itself be passed as a newly minted shared capability.
- Audit support invalidation on consume/recreate and permitted writes.
  Scope-bearing observations must carry loan access requirements.

**Tests:** R12-R14/R25, repeated owner observation followed by legal mutation,
consume/refold at equal arguments, and a changed pointer-field dependency.
Preserve unrelated supported observations through the reverse index.

**Done when:** the current projection machinery has one explicit
interpretation at each consumer. Observing an owner neither freezes it
forever nor gives a borrower an untracked independent capability.

### V6 — Build the joint call-resource plan

**Read:** D6, D8-D9; current unification transition APIs. **Depends on:** V5.

**Boundary:** `prepare_contract_resource_transfer`,
`CFunctionResourceTransfer`, and their shared requirement/effect helpers in
`src/kernel/functions.rs`; call-plan tests. Leave actual return orchestration
to V7.

**Work:**

- Separate evaluation/obligations, proposed partition, and checked commit.
  Reuse validated `CResourceSpec` metadata and dependency-aware lowering.
- Plan all clauses jointly, with identical/overlapping views sharing backing
  and owned/viewed overlap requiring an actual legal partition.
- Record entry-selected dependent pointers, caller residuals, escrow,
  callee access, scope binding, owned transfers, and restoration obligations.
- Derive the mutable effect projection from the committed transfer.
  Candidate rejection is transactional and preserves provenance.

**Tests:** R06-R08/R11, two identical views, partially overlapping views,
one unknown-alias read pair with common covering owner, views with disjoint
writable residual, clause-order variants, and a later clause failing after
an earlier candidate would have lent memory.

**Done when:** the same plan representation can serve ordinary and named
contracts. A view output is backed by checked access, and no separation fact
is assumed just because two clauses appeared in the input.

### V7 — Bind direct calls and recover on returns

**Read:** D8-D9 and staging contract. **Depends on:** V6.

**Boundary:** direct function entry/call/return paths in
`src/kernel/functions.rs`, generic function contract certification inputs,
and the minimum surface entry-lowering adapter.

**Work:**

- Instantiate generic view inputs as the single shared access environment
  from D8, with one call scope and possibly several parent dependencies.
  Check actual-call substitution against the V6 plan.
- Pass owner-backed views by lending; pass existing views by checked share
  transfer/reborrow. Recover only scopes this call created.
- Replace ensured-view deduplication as a recovery mechanism with checked
  return obligations. Preserve normal borrowed ownership semantics.
- Handle early/ordinary returns and nested/recursive read helpers; reject
  unexpressible escaping access rather than silently ending it.

**Tests:** R01/R06/R09/R18/R24, reader-then-write/free, caller retaining an
outer view, two aliases, and a callee unable to close its caller's scope.
Check postcondition evaluation before access discharge.

**Done when:** the simplest actual C reader calls exercise the new rules
through the shared engine and certificates. No new public lifetime syntax
or proof-only local C changes are needed.

### V8 — Route callbacks and contract refinement through the same rules

**Read:** D8-D9; V7 APIs and callback support map. **Depends on:** V7.

**Boundary:** named/indirect call application, refinement, explicit execution
theorem adapters, and their contract/proof tests. Avoid changing unrelated
callback matching/search heuristics.

**Work:**

- Route every body-independent contract application through V6/V7.
  Preserve exact pointer contract evidence and current support provenance.
- Implement checked own-to-view adaptation for interface refinement;
  reject the reverse when only a stable view is supplied.
- Prevent reentrant callback access to suspended caller authority.
  Verify effect summaries cannot havoc the loan's protected footprint.
- Confirm automatic formation and independently certified execution
  theorems use the same authority transformations.

**Tests:** R18-R21 on direct, named, indirect, theorem, and refinement paths;
real callback-table retained-cell witnesses plus permitted-mutation negatives.

**Done when:** the path inventory has no alternate contract engine using
legacy view consumption for a scope-bearing state. Failure identifies the
conflicting contract clause/loan, not a guessed callback target.

### V9 — Protect local storage and allocation lifetime

**Read:** D6, D10; V7 entry/return APIs. **Depends on:** V7.

**Boundary:** `src/kernel/eval/statements.rs`,
`src/kernel/eval/memory_loads.rs`, relevant helpers in
`src/kernel/primitives/memory_state.rs`, and the caller-local lending
shortcut in `functions.rs`. Coordinate the last file with V8 if needed.

**Work:**

- Replace implicit local permission bypasses with internally tracked
  local authority/suspension, preserving ordinary local syntax.
- Apply read/write checks to supported scalar/aggregate/byte paths and
  materialized aliases. Keep bounds/initialization independent.
- Reject free/realloc/lifetime end with live loan dependencies, including
  hidden descriptions and subrange loans. Preserve allocation tokens.
- Protect against reused local names or heap addresses reviving descriptors.
  Audit static/global/literal special cases and record their justification.

**Tests:** R09-R11/R31 with concrete live storage; direct local assignment
and indirect alias store while lent; a legal write after return; heap
subrange loan, realloc, and stale generation.

**Done when:** no `local:` or external-memory classification can bypass
the loan law. Missing-allocation rejection is not counted as the live-loan
free regression.

### V10 — Preserve loans through loops and branches

**Read:** D9-D11. **Depends on:** V8, V9.

**Boundary:** `src/kernel/loops.rs`, relevant checked execution branch/join
paths, and focused C/Proof regressions.

**Work:**

- Audit `loop_body_resource_context`, automatic viewed forms, invariant
  entry/backedge comparison, and loop memory-effect summaries.
- Retain outer view dependencies, close iteration-local scopes, and reject
  implicit invention/forgetting of access at the backedge.
- Include loan deltas in branch joins. Reconcile branch-local scopes only
  after checked discharge; keep incompatible surviving states separate.
- Ensure early returns and non-returning paths have the D9 behavior.

**Tests:** R22-R24; zero and multiple iterations, nested reader call inside
an owning loop, view-only loop, disjoint mutation, same-value loop havoc,
and one branch retaining a share. Re-run existing loop resource fixtures.

**Done when:** neither invariant reconstruction nor proof branching is a
way to duplicate access or recover early. Joins use changed-state evidence
rather than complete-history comparisons.

### V11 — Preserve dependencies through composite resource operations

**Read:** D6-D7, D11-D12. **Depends on:** V5, V7, V10.

**Boundary:** `src/surface/proof/resources.rs`,
`src/surface/proof/proof_object/resource_steps.rs`, their kernel rewrite
checks, and population/body helpers.

**Work:**

- Carry loan/support bundles through fold, unfold, observe, scoped open,
  close, symbolic resource pieces, and counted population bodies.
- Make viewed body projections read-only. Suspend a folded parent's
  alternate authority while its pieces are lent or exclusively exposed.
- Pin access while a borrowed body is open, and check closure restoration
  before returning it. Prevent hidden obligations from escaping via a head.
- Reassemble caller packaging only after resource facts in the resulting
  state are checked; preserve legitimate changed model arguments.
- Keep exclusive-instance views unsupported and token quantities conserved.

**Tests:** R13-R17/R25, nested folded view, open-with-live-body at scope
end, partial-field loan from a folded owner, and counted remaining units.

**Done when:** every current resource operation either preserves required
dependencies or explicitly refuses the unsupported case. Resource
abstraction cannot conceal an active reader from recovery.

### V12 — Allow stable viewed memory to support resource facts

**Read:** D7 and the existing definition-validation coverage rules.
**Depends on:** V11.

**Boundary:** `src/surface/validation/definition_validation.rs`, dynamic
fold/observation checks, and paired resource-definition/proof fixtures.

**Work:**

- Extend static coverage to properly scoped views while retaining owned
  coverage and current guard/bounds/predicate-load analysis.
- Dynamically capture the actual loan dependencies when proving/folding
  a fact about viewed memory.
- Keep persistent scalar facts and snapshot facts distinct from current
  memory facts requiring active support.
- Reject attempts to store the fact in an output resource whose interface
  cannot retain the required scope.

**Tests:** R12/R15/R16 with a zero-valued cell, symbolic in-bounds element,
nested support, uncovered neighboring element, false value, ended scope,
and a predicate-hidden read. Re-run all previous coverage rejections.

**Done when:** the intended stable-view resource example verifies and
each dependency-erasure attempt fails in the kernel as well as validation.

### V13 — Migrate the minimal C examples and classify view outputs

**Read:** D1, D6-D9 and V0 inventory. **Depends on:** V8, V9, V12.

**Boundary:** the smallest sidecar/mdtest contract migrations, paired
rejection fixtures, and any narrow output-lowering diagnostic needed for
the already chosen supported boundary. No C implementation edits.

**Work:**

- Migrate aliased sequential read/write examples to truthful ownership
  contracts; preserve valid aliasing rather than adding false separation.
- Migrate whole-resource-view plus owned-field cases to selected field
  views or whole ownership with precise guarantees.
- Audit every explicit view-producing/output form in the V0 inventory.
  Classify existing outer dependency, returned input access, immutable
  support, or currently unsupported escape; implement no implicit new
  escaping lifetime language.
- Add concise ordinary reader, nested-reader, partial-borrow, and
  view-supported-fact examples using the normal proof workflow.

**Tests:** R06-R09/R15/R24; small synthetic returned-pointer C example must
remain legal when the caller independently retains authority.

**Done when:** minimal C usability is demonstrated under the candidate
semantics and positive C sources are byte-for-byte unchanged. No blanket
replacement of `views` by `owns` has removed shared-reader coverage.

### V14 — Recheck extension models against implemented rules

**Read:** D2-D5, D12, concurrency section and shared language design.
**Depends on:** V4, V11.

**Boundary:** the small model, kernel/model correspondence tests, and a
design handoff. No threading API, Rust frontend, mutex library, or atomics.

**Work:**

- Map every implemented shared-loan model step to its checked kernel
  operation and compare outcomes on representative traces. Do not replace
  the independent model invariant with calls to the implementation's
  own validity helper.
- Add shared/exclusive reborrow and returned-field-loan dependencies.
  Exercise updated-value recovery and forbidden parent access.
- Model two-context partition/transfer/join, disjoint writers, a mutex
  invariant/guard, and a thread-local mutable-cell protocol.
- Record abstract memory/scheduling assumptions, bounds, omitted language
  rules, and extension-only operations. Give preservation arguments for
  the added transitions and explain the shared-kernel correspondence.

**Tests:** R27-R30 plus the original two-reader trace with each reader
placed in a different context.

**Done when:** the model can express these cases without weakening the
implemented stable-view rules or equating lifetime with lexical scope.
A contradiction triggers a bounded design correction before V18; a passing
sequential interleaving model is not a release/acquire proof.

### V15 — Complete proof tools, semantic identity, and diagnostics

**Read:** D13 and the path inventory. **Depends on:** V8, V10, V12.

**Boundary:** surface proof-object adapters, expansion/audit/profile plumbing,
diagnostic formatting, and cache/certification identity at the existing
shared engine boundary.

**Work:**

- Ensure generated simple proofs/call certificates check loan transitions.
  Preserve original source attribution and selected resource names.
- Add the D13 refusal categories with bounded context and useful origin
  links. Missing separation and proven overlap remain distinguishable.
- Bind prepared proof/cache artifacts to the resource-semantics identity
  while staging; a stale legacy result cannot certify the new claim.
- Exercise actual verify, expansion/reverification, profile, and audit using
  shared APIs. Do not construct recursive CLI subprocess workflows.

**Tests:** R26 across direct, callback, local, loop, and composite fixtures;
tampered/cross-interpretation evidence and diagnostic-size bounds.

**Done when:** all tools agree on both positive and negative witnesses,
and a failed loan rule has a local actionable explanation.

### V16 — Enforce deterministic scaling

**Read:** D4-D6, D13, R32 and the efficiency contract.
**Depends on:** V10, V11, V15.

**Boundary:** focused instrumentation/scaling tests and local fixes to the
new paths they expose. Follow `src/instrumentation.rs`,
`src/kernel/tests/resource_tests.rs`, and
`src/surface/tests/scaling_tests.rs` patterns.

**Work:**

- Add independent four-size curves from R32, including current live count
  versus accumulated completed-call count and deep split-tree reads.
- Count actual index candidates, persistent edits, support/dependency
  changes, certificate deltas, and tree joins.
- Exercise explicit simple proofs so search improvements cannot mask
  checker complexity. Separate unavoidable selected-body traversal.
- Repair only demonstrated hot-path violations; preserve semantic tests.
  If the fix needs a representation change outside this card, return a
  concrete blocker and revised boundary rather than raising the budget.

**Done when:** deterministic curves meet the stated local/total bounds,
all results still verify, and the full gate passes. Wall-clock gains alone
do not close this card.

### V17 — Migrate the corpus and preserve rbtree readiness

**Read:** V0 inventory, V13 patterns, and current rbtree/callback milestones.
**Depends on:** V13, V15, V16.

**Boundary:** existing sidecars, resource contracts, test expectations, and
example documentation affected by the semantic change. No C source edits.

**Work:**

- Process the inventory by class, with reviewed explicit diffs.
  Preserve both aliased-reader clients and legitimate sequential writes.
- Cover real current rbtree helper/callback footprints; do not replace them
  with synthetic simplified C or require unrelated rbtree milestones.
- Reclassify weak-view-positive fixtures: add their truthful stable
  contract counterpart and retain a concrete rejecting old-contract caller
  where it tests a meaningful invariant.
- Run the complete candidate-semantics corpus through normal engine paths,
  including stdlib, mdtests, examples, and compiler-import fixtures.
  Explain any previously supported view-output form that needs a contract
  change or is now explicitly outside the supported lifetime interface.

**Done when:** the inventory has an outcome for every class/file, all
candidate gates pass without skip lists, and every C-source difference is
absent or independently justified under repository policy. Record remaining
unrelated rbtree blockers without claiming this issue finishes the demo.

If the inventory is large, the coordinator may subdivide this card into
nonoverlapping fixture directories/classes using the same R IDs and handoff
format. These are subtasks of this issue, not new issues; each subdivision
must preserve green checkpoints and must not change shared kernel semantics.

### V18 — Review the complete change adversarially

**Read:** this entire issue and all implementation handoffs.
**Depends on:** V14, V17.

**Boundary:** review and minimal missing regressions/fixes; no new features.
Assign after implementation, preferably to an agent that did not author the
core loan rules. This card does not start such an agent now.

**Work:**

- Check every D2 law against all V0 entry-point consumers. Search for old
  core projection, non-consuming view satisfaction, owner/view absorption,
  return deduplication, local bypass, loop viewed form, and unchecked resource
  rewrite paths. Classify each remaining occurrence explicitly.
- Try to duplicate authority through facts, normalization, substitution,
  branch joins, hidden resource bodies, counted units, and stale snapshots.
  Recheck R01-R32 coverage at its required layer.
- Verify that the full candidate engine has no legacy fallback and that
  extension-model claims match implemented versus model-only operations.
- Review scaling evidence and the planned V19 removal list. Run the full
  candidate gate on the exact reviewed commit.

**Done when:** all required semantics have an enforcing path and meaningful
regressions, every observed defect is fixed/rechecked, and the coordinator
has an explicit cutover-ready verdict. Unresolved soundness or tooling
concerns block V19; an optimistic checklist does not replace evidence.

### V19 — Cut over, document, and close

**Read:** V18 verdict/removal list and final acceptance below.
**Depends on:** V18.

**Boundary:** default entry interpretation, removal of temporary rollout
scaffolding, public docs and affected expectations; no new semantic design.

**Work:**

- Make stable views the sole ordinary-memory interpretation. Remove
  legacy independent view creation/fallbacks and temporary mode selectors.
  Retain only justified owner observations, scoped views, and explicit
  family-specific persistent facts.
- Update `docs/concepts/resources.md`, affected examples, proof/tool docs,
  and the stable-versus-historical descriptions in the shared language
  design. Explain temporary stability, owner reads, partial borrowing,
  scoped recovery, and supported escaping-output limits.
- Preserve the final rules, representation rationale, model assumptions,
  and test map in durable resource/internal documentation before deleting
  this issue. Future agents must not lose the design when the issue closes.
- Run focused changed tests and the unfiltered `scripts/check.sh` on the
  final default configuration. Check the clean primary base and integrate
  only the tested coherent commit.
- Delete this issue and its README entry only when all final acceptance
  criteria hold. Update links that pointed to it.

**Done when:** stable memory views are actually enforced everywhere in the
supported C verifier, the rollout path is gone, the docs describe shipped
behavior, the full gate passes, and the rbtree launch remains the roadmap.
If V19 requires a new semantic fix, return it to the relevant card and rerun
the affected review; do not improvise it inside the final documentation step.

## Concurrency and Rust design checks

Build a small checked resource-transition model for the matrix below before
adding a production threading or Rust frontend. Include memory steps and
context splitting: asserting flags on a proposed loan struct is not evidence
that resource composition prevents races. Each step must preserve the rights
held in the other context. [Iris, frame-preserving updates](https://iris-project.org/tutorial-pdfs/iris-lecture-notes.pdf)

Exercise an exclusive parent loan with a shared child and an exclusive child.
The latter must suspend conflicting parent reads as well as writes. Include
a borrow returned into a caller-owned field and recovery of that field's
updated value. Keep access-origin checks, source reference types, object
lifetime, and loan expiration distinct. The compiler evidence and detailed
C++/Rust interpretation now live in
[Supporting more languages](../design/supporting-more-languages.md#borrowing-complications-to-revisit-for-rust).
The existing probes remain regression inputs for this issue's model.

Use one mutex-like protocol as a check on abstraction. Its shared handle
grants the right to acquire a guard; protected memory is owned by the invariant
until acquired, and returned on release. Two handles must not project raw
payload views or duplicate payload ownership. A thread-local mutable cell
needs a different sharing protocol; allowing interior mutation does not
itself justify cross-thread access. Language/library interpretation is
recorded in the shared design document.

Copyability alone must not authorize moving an abstract view to another
thread. Its sharing interpretation must justify that transfer; test a
thread-local cell protocol alongside the transferable mutex handle in the
model. This leaves a place for Rust's type-dependent thread-safety rules.

The first release need not add customizable sharing predicates, Rust trait
checking, or production locks. Keep the family sharing operation separate from
unconditional recursive projection of owned bytes. Unsupported abstract
sharing must fail explicitly. Atomics, ordering, and Linux RCU remain in
[concurrency-and-atomics.md](concurrency-and-atomics.md); a small
release/acquire publication example is a memory-model design check, not a
claim established by stable views or by sequential interleaving alone.

## Intended regressions and acceptance criteria

The smallest semantic regression uses ordinary memory `x` initially 0:

```text
owner lends x into scope k
reader A receives View(k, x), Live(k, 1/2)
reader B receives View(k, x), Live(k, 1/2)
both read 0; lender's store/free/end-scope attempt fails
both return their live shares; end k; recover ownership once
store 1 succeeds; any retained View(k, x) fails to authorize a read
```

This is a proposed kernel/model regression, not supported threaded C syntax.
It must fail under a naive extension of current owner-plus-view composition
and pass under the new checked rules. Also cover:

| Case | Required result |
| --- | --- |
| Call a read helper, then mutate/free | Pass, with automatic scoped recovery. |
| Two aliased read parameters or nested read helpers | Pass without requiring their separation. |
| Store via another alias during a shared loan, including a same-value store | Reject, including through callbacks and stack aliases. |
| View one field while writing a disjoint field | Pass and preserve the viewed value. |
| Branch ends a loan on only one path, or recovery occurs twice | Reject invalid join/recovery; keep valid branch-specific proofs possible. |
| Copy a descriptor, end its scope, start a new scope, then use the old descriptor | Reject stale authority. |
| Fold a view or store it in an abstract resource, then end its scope | No live access/fact may escape without the corresponding scope obligation. |
| Shared or exclusive child reborrow | Parent conflicting accesses fail until child ends; correct authority returns afterward. |
| Returned field loan | Parent recovery waits for the returned loan; mutation is reflected in the recovered state. |
| Two workers own disjoint array ranges | Both may write; shared loan restrictions stay local to the borrowed range. |
| Shared mutex-like handles | Guard acquisition transfers authority; unguarded access and duplicate guards fail in the selected protocol. |

For this P1 issue, thread contexts, Rust-style returned loans, mutable
reborrows, and the mutex protocol may be exercised in the checked model.
The supported C cases must exercise the actual verifier. New production
thread APIs, Rust syntax, and a complete unsafe alias model are not required
to close the issue; the model must explain how those extensions preserve the
implemented shared-loan laws.

For contract-overlap negatives, include a concrete caller with live allocated
memory. Proving a function under an inconsistent `owns`/`views` precondition
does not test rejection of the bad call. Diagnostics must identify the
conflicting loan and range instead of silently treating the input as a valid
borrow or fixing the proof with an unjustified separation assumption.

Acceptance requires:

- V0-V19 have integrated handoffs, all D2 laws have enforcing paths, and
  R01-R32 have the required positive/negative evidence at their stated
  layers. Preserve the result map in durable documentation before closure.
- Stable views are the default and sole ordinary-memory interpretation.
  No legacy fallback, temporary rollout selector, stale proof/cache result,
  or alternate verification entrypoint can bypass the checked loan rules.
- The stable ordinary-memory semantics, borrow extent, composition laws,
  recovery, and distinction from owner-supported observations are documented
  and enforced in the kernel. The small model's exact assumptions and its
  relationship to implemented rules are recorded; no claim of a complete Rust
  alias model or C concurrency model is made.
- Calls, callbacks, loops, local memory, resource abstraction, and certificate
  validation share those rules. Representative ordinary verification,
  expansion/reverification, and audit results agree.
- Migration positives and negatives above have focused automated regressions;
  existing C sources remain unchanged. Both read sharing and legitimate
  sequential alias mutation remain expressible without proof-only C changes.
- Deterministic four-size regressions vary loan count, nesting depth, repeated
  read calls, and unrelated resources independently. Loan lookup/closure and
  permission splitting touch the affected loan/dependency delta, with indexing
  overhead, rather than scanning/cloning the whole state or all historical
  view copies. Fraction representation costs must also be bounded by the
  explicit certificate; the initial binary share tree must not hide
  quadratic identity/path handling behind constant-size token names.
- `scripts/check.sh` passes. Update resource docs and affected fixtures when
  semantics land, preserve the implemented design outside this issue, then
  delete this issue and its list entry.

## Coordination

[memory-vs-resources.md](memory-vs-resources.md) remains a P1 refactor preserving
current semantics. Reuse its unified transitions and support provenance;
coordinate representation boundaries now. The efforts may share implementation
work, but stable views must be an explicit, tested semantic change, not an
accidental side effect of unification. This issue owns stable shared-memory
views and their loan protocol; the shared-permission item in
[resource-algebra-extensions.md](resource-algebra-extensions.md) should use
these rules rather than develop a competing meaning of views.

The [basic C++ issue](basic-cpp-support.md) consumes the stable access and
lifetime-transition APIs; its constructor/destructor work must not implement
a second loan ledger. The [goto issue](goto.md) consumes explicit scope-exit
obligations when control flow needs them; completing general goto is not a
prerequisite here. Production threading, atomics, Rust syntax, and arbitrary
escaping-borrow syntax remain outside this issue. Coordinate these boundaries
through [Supporting more languages](../design/supporting-more-languages.md)
and keep rbtree as the launch demo.
