# P2: Stabilize and deliver the shared object model

Priority: P2.

Soundness: soundness-adjacent. This work changes the evidence used to justify
object access, pointer designation, initialization and modular transfer across
C, C++ and Rust. The accumulated implementation has unresolved compatibility
failures and an incomplete admission audit. This issue does not demonstrate a
new false acceptance. Reproduced soundness defects retain their own P1 bugs and
must be repaired or explicitly refused before affected support is claimed.

## Purpose and ownership

Deliver the accepted bounded object model as independently reviewable, green
changes, and recover the oversized work accumulated around
[PR #646](https://github.com/clicklang/click/pull/646). Freeze new C++ feature
admission while establishing this foundation. Completion means a checked model
with demonstrated language boundaries and preserved existing behavior, rather
than an ever-growing collection of successful helper proofs.

This issue owns the shared semantic design, baseline audit, decomposition,
delivery sequence and completion ledger. The detailed laws and operation audit
remain in [C++ object model and shared memory semantics](../design/cpp-object-model.md).
[Aggregate construction](../design/aggregate-construction.md) records the
construction/return protocol. Their implementation claims must be checked
against the revision they describe before being presented as upstream behavior.
[cpp-support.md](cpp-support.md) owns subsequent C++ coverage and Bitcoin Core
milestones; [rust-support.md](rust-support.md) owns Rust coverage.

## Recovery starting point

The preserved implementation checkpoint is `b92deef95` on
`codex/cpp-object-model-design`, including upstream `325f9f604`. At that
comparison the branch has 60 branch-only commits and changes 249 files, with
about 62,700 added lines. These measurements describe the local accumulated
branch, not necessarily the head currently published on #646.

The last normal example-project run on this checkpoint passes 35 of 52 projects
and fails 17. Four selected kernel tests, four selected C++ tests and six
Markdown fixtures pass; selected expansion/rewritten/retained checks, Clippy and
documentation checks also pass. These are partial results. No green-tree verdict
has been established for the checkpoint, and its failing projects have not been
systematically classified against the same master baseline. Seventeen projects
are not evidence of seventeen independent defects.

Preserve the full Git history, design decisions and reproductions. Use this
branch as an archive and source of candidate changes. Keep new delivery work in
separate worktrees rooted in an identified upstream revision.

## Accepted semantic design

Retain typed cells, allocation identities, immutable snapshots and indexed
resource ranges. Share operations and checked evidence between execution,
logical observation and modular proofs. Frontends supply explicit language
rules and authenticated source metadata; source spelling or matching numeric
addresses cannot manufacture semantic evidence.

| Component | Required meaning | Independent obligation |
| --- | --- | --- |
| Storage | Allocation identity/generation, live extent and alignment | Existence of an object of the requested type |
| Object and place | Declared/admitted type, containing object, subobject or array domain, lifecycle phase | Initialization and access authority |
| Pointer value | Address plus retained origin/designation, position and relevant lifetime evidence | Permission to read or write its referent |
| Representation | Typed values and byte observations of the same object at a selected snapshot | Legality of every source-language access type |
| Initialization and value | Written/initialized bytes, available value and language-specific value validity | Ownership and a particular asserted value |
| Authority | Checked ownership, view or loan for the actual footprint | Object creation, initialization or pointer origin |

Unknown initialized contents and uninitialized contents remain distinct. Value
forgetting preserves established initialization and object identity; control-flow
joins retain only justified common guarantees. Copying a self-pointer preserves
its original referent. Address equality supports alias and frame reasoning while
remaining separate from complete pointer identity and typed-place validity.

Use shared `valid_place(p)` and `valid_place(p[0..n])` for typed-place validity.
They grant neither ownership nor initialization. `owns` and `views` retain their
access meanings; a view alone does not assert that arbitrary storage contains
an object of a requested type. Initialization effects remain explicit,
body-checked postconditions and transfer separately from ownership and value
claims. Merely mentioning an output read in a proposition cannot initialize it.

Construction uses the exact caller-selected destination. Storage allocation,
construction completion, ordinary value copying and lifetime end are distinct
operations. Construction does not imply freshness or separation. Check the
actual read/write footprints; require padding authority only when the operation
accesses padding. Assignment materializes a separate RHS where the admitted
source semantics require it. Already supported cleanup remains supported.

### Language boundaries

- **C:** retain explicit allocated-storage/effective-access rules and the
  existing verification boundary for ordinary C. C++ object requirements must
  not activate merely because the C frontend knows a struct layout. Preserve
  existing valid C sources and claims, including nullable resource bodies,
  allocation, pointer fields and modular callers.
- **C++:** native references, declarations and checked importer identities can
  supply appropriate place evidence. Preserve phase-specific construction and
  lifetime rules, supported subobjects, bounded copy-equivalent construction
  returns, assignment temporaries and existing RAII/unwind behavior. A native
  signature's promise must be checked at actual calls as well as assumed at
  symbolic body entry.
- **Rust:** reuse shared storage, initialization, representation and transfer
  operations while keeping move availability, drop and borrowing rules explicit.
  Existing fixed-array, iterator, constructor and loan behavior must retain its
  meaning; importing C++ lifetime rules into Rust is not a compatibility fix.

The selected C++ profile remains pinned Clang 19.1.7, C++20,
`x86_64-unknown-linux-gnu`, LP64 and little-endian eight-bit bytes. The bounded
uint32 representation-access guarantee is explicitly an implementation
assumption, identified by `clang19_1_7_lp64_le_declared_uint32_bytes_v1` and
checked in imported artifacts. Authenticate `std::byte` by its pinned
nominal declaration while using native integer contract values. An unrelated
enum with the same width receives no representation-byte privilege.

Keep the approved native cast and shared scalar-initialization semantics.
Their implementation and delivery status belong in the audit; reopen a design
choice only for a concrete contradiction or a newly selected source behavior.

## Recovery and delivery sequence

### 1. Preserve and classify before repairing more examples

- [ ] Record the archived branch/commit, published #646 head, fixed master
  baseline, compiler/tool versions and selected fixture/artifact identities.
- [ ] Inventory the accumulated changes by semantic responsibility and
  dependency. Separate proposed laws, implementation, isolated bug fixes,
  importer coverage, tests, documentation and compatibility adaptations.
- [ ] Run the normal gate on the fixed master baseline and the candidate tree
  under comparable conditions. Use the same unchanged programs and claims;
  prepare revision-compatible artifacts from the same pinned inputs when
  schemas differ. Branch-only feature tests are coverage, not baseline regressions.
- [ ] Create a checked failure ledger: test/program, master result, branch
  result, exact command, error/trace, responsible change or smallest reproducer,
  classification, owner and required acceptance checks.
- [ ] Classify each failure as an upstream defect, branch regression, necessary
  semantic narrowing, incorrect fixture/contract, missing selected coverage or
  unresolved evidence. Establish language evidence before claiming source UB.
- [ ] Group demonstrated shared causes and locate the introducing change with
  reduction, selective reversal or bisect in a throwaway worktree. Preserve the
  archive; avoid changing several semantic layers in one debugging experiment.

Normal-gate comparison establishes the baseline. Run only the few affected
nightly fixtures by name; the nightly workflow owns the full nightly suite.
Use unchanged test definitions or comparable source-level probes when tests
moved between gate and nightly. Report timeouts and budget failures as failures.

### 2. Extract the first independently green deliveries

Prioritize reproduced P1 soundness defects, including the
[scalar-subobject pointer defect](../bugs/pointer-arithmetic-crosses-scalar-subobject.md).
Reproduce them on the fixed baseline and the archive before deciding which
activation changes are mandatory. Independent small fixes can land while that
work proceeds, with accurate scope and no claim that the object model is complete.

- [ ] Select the smallest useful change that reproduces on the baseline and
  has no dependency on unreviewed object-model activation. Candidate bug fixes
  include captured-pointer pointee typing and alignment-result typing, subject
  to baseline reproduction and current-master status.
- [ ] Treat entry-snapshot argument folding as a separate candidate with its
  own dependency check, original-source witness and wrong-cell rejection.
- [ ] Extract complete changes with their tests and accurate documentation.
  A historical commit is not automatically a clean semantic unit; reconstruct
  the patch when it combines concerns or depends on later fixes.
- [ ] Establish the first replacement's green result and reviewable scope,
  preserve/link the archive, then resolve #646's disposition. Follow the
  repository's one-open-PR-per-task rule: sequential replacements, no stack of
  PRs depending on an unmerged foundation. Keep #646 open while preparing this
  transition; this issue itself changes no PR state.
- [ ] Use the normal required checks, merge queue and authorized auto-merge for
  each delivery. Verify landed commits reached upstream before starting the
  next slice from updated master.

Every implementation slice has a stated invariant, prerequisites, positive and
negative witnesses, appropriate local checks and an explicit supported profile.
Required CI supplies the full gate before merge. Known branch regressions must
be fixed or their introducing change excluded from that slice. A new contract
restriction needs a demonstrated semantic reason and explicit accounting of
compatibility; silently weakening old claims or relabeling failures is not an exit.

### 3. Deliver the shared foundation in dependency order

The following groups are work to account for, not a fixed number of PRs or an
instruction to implement each as one patch. The dependency inventory determines
which parts can land independently and which must form an atomic change.
Credit already landed implementations and existing tests when the audit shows
they satisfy a law. This sequence does not require rebuilding those mechanisms
or migrating all three frontends in one PR.

- [ ] **Operation and evidence audit:** identify storage, layout/type, domain,
  lifecycle, initialization and authority evidence for every admitted operation.
  Audit declarations, construction, copying, moves, typed/byte reads and writes,
  casts, havoc, branch joins, cleanup and lifetime end.
- [ ] **Object/storage and construction:** make layout/subobject evidence,
  destination binding, construction completion and retirement coherent. Preserve
  existing C aggregate returns and Rust construction behavior. Keep bounded C++
  copy-equivalence admission and exact destination checks.
- [ ] **Initialization and observations:** preserve unknown initialized values,
  compressed initialized ranges and explicit output effects. Make the declared
  uint32 typed/byte bridge describe one value at one snapshot; partial writes
  update only their selected bytes and a no-op writer establishes no new output.
- [ ] **Pointer designation and transport:** retain complete pointer evidence
  through address formation, arithmetic, copying, storage/reload, casts, calls,
  resources, substitutions and snapshots. Reject cross-subobject access,
  unjustified array traversal, one-past dereference and expired objects. Address
  observations remain useful without establishing executable typed access.
- [ ] **Entry, resources and modular calls:** assume explicit input promises at
  symbolic entry and check them at actual calls and resource creation. Preserve
  full aggregate/pointer values, selected conditional bodies, mutable descriptor
  entry bindings, returned initialization and the caller's frame. Ordinary C
  metadata must retain its approved compatibility boundary.
- [ ] **Frontend activation:** enable each admitted language/profile only after
  its shared dependencies and positive/negative call controls pass. Unsupported
  cases receive bounded, specific refusals. Existing source profiles must not
  acquire C++ requirements accidentally.
- [ ] **Proof and performance parity:** independently recheck ordinary proofs,
  expansion and rewritten proofs, retained sessions and summaries. Protect local
  operations with deterministic multi-size tests, including growing unrelated
  state. Keep typed cells and intervals compressed; no global environment/history
  scan per step and no raised limits to hide a regression.

Keep reusable inactive machinery behind a checked activation boundary only when
that separation is demonstrably sound. If pointer representation, equality,
transport and access checks depend on one another for soundness, land that
minimal dependency closure together rather than exposing an intermediate model.

### 4. Close compatibility failures and the bounded milestone

The initial ledger must account for these observed groups, without assuming a
cause or that each is introduced by this branch:

| Observed group | Existing reproduction or check |
| --- | --- |
| Pointer-field frames and stored values | [C frame bug](../bugs/c-pointer-field-postconditions-lose-frame-evidence.md); original owned-vector and owned-string projects |
| Nullable allocated resource bodies | Original allocated-linked-list and heap-object projects |
| Borrowed/owned buffer and cursor transfer | Original arena, detachable-buffer, owned-segmented-buffer, owned-split-buffer, input-cursor, binary-tree, concurrency-fork-join, multifile-registry and ring-buffer projects |
| Other C proof failures after upstream integration | Original refcount and rbtree-augmented projects |
| Rust availability/ranges and proof cost | Original rust-chunks-exact and rust-byte-sum projects |
| Importer and proof scaling | Existing record-inventory multi-size work assertion, growing-place graph test and affected decoder audits |

- [ ] Give every observed failure a baseline classification and resolve each
  regression attributable to the delivered slices. File reproduced defects in
  `bugs/` and remove their files once fixes, regressions and documentation land.
- [ ] Complete the [bounded acceptance matrix](../design/cpp-object-model.md#stabilization-work-and-exit-criteria)
  with named evidence: representation, modular transfer, destination/copy,
  aliasing/frames, lifetime/availability, typed access, proof modes and scaling.
- [ ] Verify the unchanged pinned Bitcoin `ser_readdata32` source and helper
  with exact word value, initialization, span bounds and backing-lifetime claims,
  including modular, expanded and retained checks. Its already passing local
  proof is an acceptance witness, not a substitute for shared compatibility.
- [ ] Record which invariants and fixtures landed in which upstream commits,
  remove resolved bug documents, reconcile implementation claims in the design,
  and move the next C++ feature work back to `cpp-support.md`.

## Small intended regression

Use the existing [entry-count cell fixture](../mdtests/resource_uint64_entry_cell_fold.md):

```c
int32 probe(int32* p, uint64* count, int32 input) {
    *count = *count - 1;
    p[*count] = input;
    return input;
}
```

Its resource owns the original last cell, with the backing pointer and original
count captured at entry. Decreasing the descriptor must not move the ownership
promise to a different cell. The proof unfolds, executes and folds using the
entry count. The [wrong-index counterpart](../mdtests/resource_uint64_entry_cell_fold_wrong_index.md)
must fail, and a view-only counterpart must reject the write. These fixtures
exercise a shared operation with ordinary C before relying on the C++ span
adapter. Reuse existing C++ span/caller and Rust range tests for their distinct
language boundaries; do not manufacture duplicate coverage for the checklist.

## Scope and design decisions still requiring evidence

Placement construction/storage reuse, overlapping unions, general inheritance
and virtual dispatch, broader exceptional construction, arbitrary owning
containers, concurrency and additional target profiles remain outside this
bounded milestone. Full contracts for integer-carried pointer origins remain
in the separately requested P2 [origin-contract issue](integer-pointer-origin-contracts-design.md),
including its provisional `pointer_origin` predicate and specific rejection
controls. They are not prerequisites for merging unrelated green slices.

Implementation structure and extraction order are engineering work. Ask for a
new design decision when a concrete case would change an accepted source-language
promise, choose a new compiler guarantee or contract surface, or enlarge this
bounded profile. Do not reopen the model merely because a proof is difficult.
Trace presentation changes continue to follow `AGENTS.md` approval requirements.

This issue is complete when the bounded laws and audited activation have landed,
introduced regressions are closed, the acceptance evidence and supported limits
are documented, and remaining excluded features belong to their existing
roadmaps. Preserve durable design and delivery records, then delete this issue
under the normal issue lifecycle.

Upstream control: after explicitly proving the unchanged backing pointer and
using `simp` for string push's terminator, the complete upstream string/vector
projects verify. At this recovery checkpoint, that pointer equality still
rejects after the zero store, and vector still rejects its later allocation
fold. Keep reducing these archive-specific failures; upstream control success
does not activate this branch or change the 41/52 archive audit.

The split-field string reduction now identifies a narrower next blocker:
explicit append-index bounds and stored-value proofs check, but the subsequent
simple fold exhausts its work budget. Reduce and fix the
[fold performance defect](../bugs/split-descriptor-fold-exhausts-simple-budget.md)
before continuing the archive's string proof or activation. Keep the original
C, split-field resource and existing budgets; the vector allocation fold remains
separate.
