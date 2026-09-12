# P1: Give views stable borrowing semantics

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
begin scope k                         -> Live(k, 1)
lend Own(R) into k                    -> View(k, R) + Recover(k, R)
split Live(k, q)                      -> Live(k, q1) + Live(k, q2)
                                        where q1 > 0, q2 > 0, q1 + q2 = q
read with View(k, R) and Live(k, q)    -> read covered memory; retain both
end with Live(k, 1)                   -> Dead(k)
recover with Dead(k) + Recover(k, R)  -> Own(R), consuming Recover(k, R)
```

Lending requires evidence that `k` is active and moves the owned resource into
checked loan storage. `View` is a copyable description; `Live` is conserved,
splittable authority. All live shares for a scope total at most one. Ending
requires the full share and all outstanding access/opening obligations to be
closed. If an access temporarily exposes underlying resources, it holds its
live share until those resources are returned. Recovery happens exactly once
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
counts. Do not implement an unbounded scan of pointers or view copies.

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

## Implementation sequence

Start with the small checked model and counterexamples described under
concurrency and Rust design checks below, then implement steps 1-3 and rerun
that matrix against the actual kernel.
Decide the scope/share representation and its normalization laws before
changing existing proof certificates. A model result alone does not complete
this issue; the stable semantics must land in Click.

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
  explicit certificate; repeated halving must not hide quadratic arithmetic.
- `scripts/check.sh` passes. Update resource docs and affected fixtures when
  semantics land, then delete this issue and its list entry.

## Coordination

[memory-vs-resources.md](memory-vs-resources.md) remains a P1 refactor preserving
current semantics. Reuse its unified transitions and support provenance;
coordinate representation boundaries now. The efforts may share implementation
work, but stable views must be an explicit, tested semantic change, not an
accidental side effect of unification. This issue owns stable shared-memory
views and their loan protocol; the shared-permission item in
[resource-algebra-extensions.md](resource-algebra-extensions.md) should use
these rules rather than develop a competing meaning of views.
