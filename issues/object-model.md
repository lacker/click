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

The full original string project now passes all four verification modes. The
latest normal archive example audit after the graph-lock and selected read-frame
repairs remains **42/52 passing**, with the same ten compatibility failures
(136.3s harness, exit 100). This supersedes the 41/52 checkpoint and closes the
split-field fold-budget defect at unchanged limits. PR #1051 delivers the
bounded byte-gap and graph-lock repairs upstream; its final pushed head
`9d6ac45c2` is verified in upstream history. The discarded final-assumption trace
fix is delivered in PR #1054; both pushed commits `7350af8a0` and `09c1cf285`
are verified in upstream history.

Continue with the separate vector allocation fold. Address equality is available
there, but the full loaded pointer values differ across the modular push call.
The selected read-frame repair closes a separate checked-unfold delta mismatch;
its focused reduction passes all four modes and 337 selected controls pass.
Neither that reduction nor the passing upstream C examples establish archive
activation. Keep original C, contracts, split-field resources and budgets intact.

PRs #1055 and #1058 deliver the selected full-read bridge for loadability and
contained-range deltas upstream; final heads `61c6ae286` and `19b3739ea` are
verified in upstream history. The archive's next native-prefix repair preserves
a uniquely indexed live input witness's original coordinates through checked
complete-read frames. Its refold-and-return reduction passes all three proofs
and all four proof modes; 220 related controls pass, including deterministic
multi-size lookup and rejection controls. This is an archive checkpoint, not an
upstream activation. The adjacent refold-and-free reduction still rejects exact
allocation-spelling lookup, and the original vector comparison remains open.

The adjacent refold-and-free reduction is now repaired as well: selected read
history discovers the held allocation owner, full pointer-value equality checks
it, and retirement uses its original coordinates. The native-input witness is
retired along with the allocation. Both return and free reductions pass all four
proof modes; 312 related controls and 90 transfer/proof-execution controls pass.
The original two-call reduction still fails its later allocation fold after
`advance`; the original vector still fails after modular push. Investigate
body-certified preservation of an unchanged C pointer field next, without
turning numeric postcondition equality or C layout metadata into native object
authority. The last normal archive audit remains 42/52; no new audit is claimed.

The field-source prerequisite now observes an ordinary C field through existing
C member evaluation, with full-width initialization and read authority, without
admitting a native record domain. Native-only policies retain authenticated
selection. The next increment must connect checked C field candidates to
universal body certification and modular full-value transfer; numeric equality
alone remains insufficient. This prerequisite does not change the latest
original-vector or normal-audit results.

The next archive increment connects direct C input-field candidates to complete
body certification and modular transfer. A preservation equation requires an
initialized full pointer read and no overlapping write on any normal return
path; full replacement, partial overwrite and a changed branch are rejected.
It preserves the caller's complete value and qualifiers without admitting a
native record. Candidate discovery visits the selected body, field keys use
cached layout identities, and inference is shared across contract claims.
Deterministic 0/16/64/256 controls cover those costs. All 96 focused C++/effect
controls and 337 broader kernel controls pass.

Source-level activation remains blocked: the frontend names folded-input reads
that independent entry construction does not reconstruct. Keep exact independent
input checking; resolve the observation protocol rather than trusting caller
cells or promoting numeric equality. The original-vector result and latest
42/52 normal audit are unchanged.

The archive now reconstructs declaration-based observations for unconditional,
single-unit owned C input heads. It evaluates direct memory clauses in order
with scratch read authority, names their values from one fixed entry snapshot,
and attaches only read cores to the exact owned occurrence. It does not install
child ownership or accept caller-specific cell values. Borrowed and quantified
head recipes remain unsupported.

The comparison exposed frontend naming of an `int32` in the padding between
`len` and `data`. Field naming now respects the retained declaration's element
count and complete value width within the physical ownership span. Owned/viewed
scalar, array-padding and complete-pointer controls pass, including multiple
sizes. All 98 focused controls and 341 broader kernel/projection controls pass.

The original two-call reduction now passes independent entry matching and
infers the preservation effect, but stops while applying `advance`: the new
permission check sees the folded input rather than the existing checked
precondition observation state. Connect that state to preservation next. No
full-project four-mode acceptance or new normal-audit count is claimed.

Modular unchanged-field application now reuses the checked input opening
already constructed for precondition reads. Only preservation effects use that
read state; actual stores retain their original write-authority checks. The
source dependency inventory includes pointer-field readers and loop tests,
uses lightweight formal metadata and the selected body, and exports only a
boolean candidate query. Body certification remains the authority.

The original two-call reduction verifies all three proofs and passes fresh,
expanded, rewritten and retained checking. Its unchanged C and contracts are
preserved in `mdtests/c_pointer_field_preservation_across_calls.md`. All 401
selected kernel, C++, field and dependency controls pass. The original full
vector now reaches a later backing-element `transport` failure. CLI tracing
still takes a contract-scoped function-set route and lacks the checked callee
summary; the [trace-selection bug](https://github.com/lacker/click/blob/cd8a9e7df/bugs/tracing-function-selection-drops-checked-carrier-dependencies.md)
records that separate mismatch. Fix that route before using its earlier
allocation-fold failure to diagnose the full project. The normal archive audit
remains 42/52; no new audit or activation is claimed.

Tracing now uses named proof-unit verification, the same dependency boundary
as source-location verification. The separate function-set API keeps its
contract-scoped behavior. All 15 CLI trace controls pass, including a selected
caller whose unrelated sibling proof deliberately fails. The reduced C project
passes CLI tracing and all four proof modes. Trace rendering is unchanged.
The original vector trace now reaches the same backing-element `transport`
failure as ordinary verification; it stops at a descriptor-field store.
Investigate its explicit frame premises before changing memory semantics.

The modular C prefix control in
`mdtests/c_pointer_field_prefix_postcondition_across_call.md` passes fresh,
expanded, rewritten and retained checks on recovery checkpoint `1a74b09c5`
plus this fixture. It preserves the original vector-push C and contract.
The grow-then-push project remains incomplete: its direct transport crosses
the callee's writable footprint, and an explicit callee-prefix `simp` exhausts
the existing control budget. Track the reproduced failure and diagnostic-only
timing evidence in `bugs/vector-callee-prefix-proof-exhausts-control-budget.md`.
Private probes and rejected proof variations are removed. No new full archive
audit has run; retain 42/52 and the same ten compatibility failures.

The checked pointer-effect return path now also publishes stateful ensures
against its final returned memory, after output checking and complete-carrier
restoration. Earlier ensure instances remain available for internal output
recovery; this does not change initialization, ownership or origin authority.
The modular C prefix control now uses exact `assumption` steps and passes all
four proof modes. All 401 selected call-contract/C++/rewrite controls pass.
The original vector still reaches the later grow-branch prefix obligation;
its nested checked-fact spelling and repeated-lowering investigation remains
separate. No full audit has run, so retain 42/52.

The nested checked-spelling repair retains transport and instantiation
conclusions in the existing persistent proof-local index, substitutes proof
binders for rewrite lookup, and freezes evaluated instantiation arguments.
Two multi-size work/rejection controls and 402 selected recovery controls pass.
The independent upstream extraction is PR #1081; its two controls, 107 logical
controls and full normal Markdown corpus (3,990 fixture records) pass.

The original vector is still open. The explicit reduced proof gets past the
previous rewrite-lowering failures but exhausts the enclosing budget. A debugger
stack locates that exhaustion inside transport's preliminary cross-snapshot
availability lookup, through typed range disjointness and memory resolution,
not in closing/publication of the `have`. Continue that selected-frame path
without changing the C, claims or budgets. No new full audit has run.

CI on PR #1081 exposed an augmented-tree Integer-certificate rendering
regression. Normalized lookup entries now live in a dedicated persistent
`checked_lowerings` cache, separate from authored source forms. Rewrite
presentation retains the original authored equality; binder normalization
serves only lookup and fresh lowering. The three regressions pin that boundary,
including preservation of an authored proof-local name. All 46 normal
fixed-state recovery controls pass with the gate stack setting; 16 nightly
tests remain skipped. The exact upstream sidecar that failed CI verifies
unchanged. The broader upstream rerun and corrected PR checks are in progress.


The opaque C value-input prerequisite now retains only an unresolved identity
matching the declaration's canonical binder. It imports no caller cells, object
geometry, native type, initialization or access permission. Five independent
entry controls pass, including unrelated-state sizes 0/16/64/256 and rejection
of caller geometry, a different unresolved identity, and a same-address resource
head with a different full value. This is a prerequisite, not a cursor fix.

The broader normal `pointer_` selection reports 472 passes, three failures and
17 ignored tests. The same selection on the preceding checkpoint `2cab205db`
reports 471 passes and the exact same three failures: untyped-pointer error
classification, the pointer-field address-equality rejection control, and
modular record-pointer identity return. The extra pass is the new identity
normalization control. These pre-existing failures remain activation blockers;
the last full example audit is still 42/52.


The stale untyped-pointer fixture used `c_pointer_value`, which now creates
an `int32*`. Its replacement checks `void*` dereference/index rejection and
GNU C byte arithmetic separately. The latter is an existing explicit kernel
policy, not a new object-model promise. The pointer-field address-equality
rejection and modular record-return failures above remain open.


All 27 pointer-result effect controls now pass, including an ordinary C identity
helper checked with a canonical opaque input and no native-input promise. Its
modular call preserves the actual scalar and one-past values exactly. Five
independent-entry controls still pass. The final broader pointer selection has
474 passes, two failures and 17 ignored controls: only the documented loaded
field/address-equality and modular declared-record identity-return failures
remain in that selection. Formatting and documentation lint pass (Vale absent,
advisory skipped). No full example audit has run; retain 42/52.


The declared C field destination selector now also supports a certified write,
checking its parameter, member path and pointer storage type exactly. It does
not read the previous pointer field or create native object authority. Existing
write permission and full-width initialization remain prerequisites. The new
control starts with initialized integer bytes, transfers an opaque pointer
value, and rejects partial storage, missing ownership, malformed selectors and
NativeObjectOnly state/interface profiles. All six field-effect controls pass.
The broader pointer selection has 475 passes, the same two known failures and
17 ignored controls. This does not yet infer the C initializer's copy effect: complete
independent body certification and modular output integration remain next.
Keep the original cursor C and contracts; no full example audit has run.


Complete independent C body certification can now discover direct pointer
parameter copies into declared C fields. A fixed-size input-identity index
selects each candidate from the final checked full value; the existing effect
checker then validates every normal return and rejects intervening overlapping
writes. It does not equate numeric addresses or infer native object geometry.
Native destinations retain their existing inference route. The new positive
control uses a legacy C destination and opaque value inputs with no native-input
promise; its branch control rejects an unconditional effect when the two return
paths store different inputs. All 28 result-effect controls pass. The broader
pointer selection has 476 passes, the same two known failures and 17 ignored
controls. No full example audit or completed cursor proof is claimed.

Next connect this checked copy recipe to source input preparation and modular
C output transfer. Preserve complete actual values, including null, legacy and
native carriers, without allowing address equality to manufacture an origin or
C allocated-access rules to admit a C++ object. Keep caller/source permissions
and output initialization separate from the value-copy effect.


Source preparation now gives direct, exclusively copied C operands opaque
value identities without marking their parameters as native inputs. Other
body uses retain their existing recipe. Modular copies preserve actual null
and legacy C values; native copies accept null without gaining a pointee
permission and still reject other undesignated values. Certified input-field
copies run before returned-view matching, after write authorization and
initialization checking. Construction/output-only fields retain the later phase.

The original initializer also exposed a canonical-entry mismatch: the source
proof includes an unconditional direct memory view from its declared read-only
head, while reconstruction retained only the head. Independent entry now
reproduces that declared projection, with exact resource checks still rejecting
unrelated views and ownership. Six entry and seven field controls pass; the
broader pointer selection has 477 passes, the same two failures and 17 ignored
controls. The new control
`mdtests/c_pointer_field_copy_preserves_borrowed_view_across_call.md` retains
the original cursor initializer, resource and contract and passes fresh,
expanded, rewritten and retained verification. The original shared pipeline
passes both initializer calls and next fails at `input_cursor_take` returning
a borrowing composite whose backing pointer is fresh. Continue that preservation
case separately. Keep 42/52 until a new full archive audit runs.


Existing certified C input-field preservation effects now run in the same
early return-image phase as direct copies, before returned-view matching.
Read authority suffices for preservation; initialization, source/full-read
evidence and the final output checks remain unchanged. The original
`input_cursor_shared_pipeline` now passes fresh, expanded, rewritten and
retained verification with its original C and proof. The broader pointer
selection still has 477 passes, the same two failures and 17 ignored controls.
Run a new normal example audit before changing the 42/52 count. A smaller caller
whose entry gives the cursor a native model identity still fails returned-view
matching; this original-project success does not close that separate witness.


The next complete normal example audit, on `07d355f0e`, still passes 42/52,
but its failure set changed: input-cursor and binary-tree are restored, while
borrowed-slice and perpetual-service newly fail. The other eight failures are
arena, multifile-registry, owned-vector, rbtree-augmented, refcount, ring-buffer,
rust-byte-sum and rust-chunks-exact. The unchanged total is not a compatibility
verdict for the latest copy-transfer changes.

The borrowed-slice reduction exposes a write-authorization mismatch: a certified
pointer-field effect checked standalone writable bytes, while the call already
transferred its mutable footprint through an opaque owning resource. The repair
uses an indexed coverage context over that checked footprint, retaining mutex,
view-partition, read-only and active-loan checks. Caller-frame ownership outside
the transfer and partial pointer storage remain insufficient. The original
borrowed-slice project passes fresh checking; its buffer pipeline also passes
expanded, rewritten and retained checking.

The service loop instead learns a C-allocated typed-prefix witness at its back
edge. Physical allocations and native object domains are unchanged. Compare
lifetime-sensitive input metadata by persistent changes, excluding only those
C access-knowledge rows and their index memberships. Native input changes,
unknown index entries and allocation changes remain rejected. Two focused
controls pass, including a deterministic changed-witness comparison with up to
4,096 unrelated native inputs. A new full example audit is still required before
claiming either regression closed or changing the 42/52 count.

The complete normal example audit after both repairs passes **44/52** in
105.27 seconds. Borrowed-slice and perpetual-service are restored, with no new
failing project; the eight remaining failures are exactly those listed above.
The service loop passes fresh, expanded, rewritten and retained verification,
and its focused Markdown control passes on both master and the archive.
All 22 native-input controls pass; the broader pointer selection remains 477
passes, the same two known failures and 17 ignored controls. Documentation lint
passes (Vale absent, advisory skipped). This remains a partial recovery verdict,
not a full green gate or native-feature activation.

The narrower cursor caller is also rejected on upstream-based `2c484f457`
for missing borrowing-composite loan backing. Keep that baseline limitation
separate from the restored original cursor project and from archive regressions.

The ring-buffer rewrite regression is reduced to a nested head containing
pointer storage and a fixed array. The second unfold cached later array reads
at an intermediate snapshot after naming the descriptor's fields. The kernel
correctly could not equate those reads with the input snapshot without further
alias evidence. Unfold/open now uses one immutable naming snapshot for the
whole body, while lowering later selectors through earlier cached fields. This
reuses the existing body-instantiation rule and changes no kernel acceptance
rule, object representation, C, contract or resource definition.

The original ring-buffer pipeline and the reduction pass fresh, expanded,
rewritten and retained checking. The new
`mdtests/c_nested_resource_pointer_body_unfold.md` passes on the archive and
upstream-based tree. Both child-overwrite controls pass. Eight of nine existing
`resource_unfold` fixtures pass on the archive; the remaining
`resource_unfold_names_unmatched_body_cells.md` still fails its later loop-exit
fold and is reproduced unchanged with the `f936e47d8` executable. Keep that
baseline failure separate from this fix.

The complete normal example audit now passes **45/52** in 109.05 seconds.
Ring-buffer is restored with no new failing project. The seven remaining
failures are arena, multifile-registry, owned-vector, rbtree-augmented, refcount,
rust-byte-sum and rust-chunks-exact. This remains a recovery checkpoint, not a
full green gate or activation of native object-model support.

The multifile-registry failure is now attributed to stale executable row
metadata: a reader of `extern const int32_t weights[][2]` retained the parser's
placeholder outer dimension after linkage selected the complete two-row
definition. Complete only row selectors rooted in the source-resolved global
whose original declaration was incomplete. Require matching scalar type, rank
and inner dimensions. Shadowing locals and complete declarations are unchanged;
the kernel still authenticates the exact complete shape and row bound.

Immutable and mutable C AST child walks now share one exhaustive definition.
The completion pass visits source nodes and indexed declarations, not unrelated
global tables per node. Three completion controls pass, including incompatible
metadata, shadowing and four-size ambient-global scaling. All ten selected
addressability controls and eleven selected array-row controls pass, retaining
the existing strict shape and sibling-row rejections.

The reduced reader and original registry result proof pass fresh, expanded,
rewritten and retained verification; all five original registry project proofs
also verify. Three Markdown controls cover the positive reader, a shadowing
local and a row beyond the actual definition. They pass on both trees; master
refuses the last case for missing read authority, while the archive rejects the
invalid row before that access. The normal archive audit now passes **46/52**
in 106.44 seconds, restoring multifile-registry with no new failing project.
Remaining projects: arena, owned-vector, rbtree-augmented, refcount, rust-byte-sum
and rust-chunks-exact. This is not a full green gate or native activation.

The refcount diagnostic follow-up is preserved in
`bugs/archive-refcount-failure-loses-proof-trace.md`: the original failure after
a modular call and control-resource open loses its checked trace prefix. Repair
or reduce that recording defect before guessing at the missing count relation.

The missing refcount trace reduces to a shared upstream bug: the early
source-have auto-miss constructed a fresh error instead of attaching the
checked proof's existing diagnostic context. Its repair preserves the failure
message and reuses the existing context/trace formatter. A minimal failing
have after a checked helper call now retains that call's facts without adding
the failed claim. Both selected call-trace controls pass on the archive; all
73 active diagnostic controls pass upstream, with nine ignored. The unchanged
refcount trace is now available and records the post-retain read equal to
`1 + amount`; its functional failure remains open. Keep the 46/52 verdict.

The restored refcount trace confirms its failing goal and the post-call value
fact use the exact same read. The amount bounds and overflow premise are also
present. A direct rewrite of `obj->refs` to `1 + amount`, followed by
`arithmetic() using` those existing premises, closes the comparison. This is a
bounded auto-search miss; the C, contracts, resource definitions and object
model are unchanged. The original pipeline passes fresh, expanded, rewritten
and retained verification with the explicit proof.

The normal archive audit now passes **47/52** in 146.33 seconds, restoring
refcount with no new failing project. The five remaining failures are arena,
owned-vector, rbtree-augmented, rust-byte-sum and rust-chunks-exact. Concurrent
local compilation affected this run's timing; the deterministic scaling
controls remain the performance evidence. This is not a full green gate or
native-feature activation.

For the rbtree open failure, reproduce the normal audit with the entry-module
`verify_c0_project` API and trace `rb_erase_augmented`. Imported contracts are
conditional interfaces in that audit. Both broad CLI checking and selected
proof-unit checking also verify the earlier `__rb_rotate_set_parents` helper,
which reaches the separately documented integer-to-pointer origin refusal
before this trace target. Do not confuse the audit's conditional scope with
verification of every imported helper.

The shared auto-have diagnostic fix landed through
[PR #1131](https://github.com/clicklang/click/pull/1131), and its pushed commit
is verified on upstream. The fixed trace and regression close the recording
bug; its archived reproduction remains available at the immutable link in the
delivery ledger. The separate refcount comparison is now completed by the
explicit proof in `cb6c3772c`, preserving all C and contracts.

The callback-open failure is a shared cache-equivalence omission: canonical
function-pointer reads use `FunctionSymbolic(load_variable)` at zero offset,
whereas the comparison recognized only integer and scaled object-pointer
loads. Recognizing that exact registered read still checks its load kind,
cell address and unchanged snapshot. Two kernel controls pass, including
wrong-cell, narrow-load, arbitrary-symbol and displaced-pointer refusals.
The original rbtree entry-module proof now passes `open` and stops later at
its result equality; retain **47/52** until the complete audit is rerun.

Adding explicit references to the callee's existing result and inorder facts
completes the original red-black tree entry proofs without changing C or any
contract. The normal archive audit now passes **48/52** in 111.13 seconds;
remaining failures are arena, owned-vector, rust-byte-sum and rust-chunks-exact.
This remains an entry-module compatibility verdict, not verification of every
imported helper, a full green gate or native-feature activation.

Rust byte-sum's two exhausted `auto` searches are replaced with the existing
`int32_add_to_integer`, `uint64_add_to_integer` and order-conversion lemmas,
then arithmetic over explicit relevant premises. Original Rust and contracts
are unchanged. The result proof passes fresh, expansion, rewritten and retained
checking on the archive. The last complete normal audit remains **48/52**;
byte-sum is individually restored pending the next complete audit.

Arena's `take` selected its guarded ownership by pure pointer equality only.
The trace retains the iterated fact after unfolding; a focused probe finds
same-width bases that the existing checked memory-read comparison proves equal,
while the pure comparison misses them. Use that shared comparison for this
address-selection question. Seven iterated-ownership controls pass (one nightly
control remains ignored), including unchanged reads across an unrelated store,
wrong-address/changed-slot refusals and flat work at four range sizes. Original
arena now passes `take` and fails later at the window fold; arena remains
unresolved and the complete audit count remains **48/52**.

Complete iterated-fact equivalence now uses that same checked pointer-read
comparison for both element and guard bases. A focused regression also consumes
the equivalent whole holding, while changed element widths and guard addresses
reject. The seven archive controls and nine upstream controls pass (one/four
ignored respectively); range-size work remains flat. The original arena fold
still fails, so this is a shared matching repair, not an arena restoration.

The complete normal archive audit now passes **49/52** in 131.48 seconds,
restoring rust-byte-sum with no new failing project. Remaining failures are
arena (window fold after the repaired take), owned-vector (post-store frame
transport) and rust-chunks-exact (iterator cursor formation). Concurrent local
compilation affected elapsed time; this is compatibility evidence, not a
performance claim, full green gate or native-feature activation.

The migrated byte-sum sidecar in `design/charon-trial/loop-headers/sum-proof.click`
now mirrors the explicit canonical proof as required by the parity inventory.
The frozen `sum.click` and source remain unchanged. Both affected upstream Rust
parity checks pass after syncing this migration copy; the fix is in PR #1144.

[PR #1144](https://github.com/clicklang/click/pull/1144) merged; all four pushed
commits are verified on upstream. Rust chunks-exact now verifies on the archive
with explicit native-to-Integer conversions for the cursor position and the
last byte's formation/read bounds. Original Rust, contracts and object-model
representations are unchanged. Fresh, expanded, rewritten and retained checks
pass, and the migrated proof copy is synchronized. The last complete audit
remains **49/52** pending a rerun; arena and owned-vector are the other failures.

The complete normal audit of recovery checkpoint `a9635866d` is now **50/52**
in 121.71 seconds, restoring rust-chunks-exact without a new failing project.
Only arena (window fold) and owned-vector (post-store frame transport) remain.
The attempted canonical-coordinate `take` change did not repair arena and was
reverted. The next investigation reuses the already-landed upstream held-owner
address-class selection repair (`a676ba284`), with its scope, width and scaling
controls; it is not a new ownership rule. No full green gate or activation is
claimed.

The upstream held-owner address-class repair `a676ba284` is now reconciled into
the recovery branch, including its transitive-alias scope/physical-width
controls, four-size scaling check and fixture. All nine selected kernel controls
and the fixture pass; documentation lint passes with the advisory Vale skip.
The original arena window fold and owned-vector frame transport still fail.
This reuses upstream machinery and does not change the **50/52** checkpoint.

The iterator proof landed through
[PR #1150](https://github.com/clicklang/click/pull/1150). Its pushed commit
`64f0f0d46` is confirmed upstream by GitHub's compare endpoint (the merge base
is that commit, with zero commits behind). Managed command-line Git credentials
subsequently failed for fetch/push; the GitHub connector still provides read
verification. Recovery work remains committed locally for a normal push when
managed authentication recovers; no alternate Git-object publication is used.


The owned-vector repair from upstream PR #1155 (`0606e4caa`) is now reconciled
into recovery: retain checked statement-effect records at structural branch
joins, then explicitly use the callee's preservation postcondition around the
capacity store. Applying the proof alone first exposed the missing structural
join evidence; bringing both parts together restores the original vector entry
module audit. C and contracts are unchanged. The latest complete audit remains
**50/52**, with vector individually restored pending a complete rerun.

A private cell-walk probe identifies arena's read-endpoint barrier as
`LoopHavoc`; the published reduction and isolation notes are in PR #1160.
The endpoint-chain experiment is reverted. Managed Git authentication has
recovered; normal fetch and push work without alternate Git-object publication.


The complete normal example audit of `df56e3e28` is **51/52** in 116.53
seconds, with no new failure. Owned-vector passes; arena alone still fails at
`arena_alloc.contract` tactic 239, the window fold. This is a failed full audit
with one known failure, not a green-tree verdict. The next reduced-proof check
explicitly establishes the current data pointer's equality to its entry value:
it gets past ownership reassembly and exposes the resource's separation-fact
obligation. Keep that distinction when diagnosing indexed supplier selection.


The original arena allocation proof now passes fresh, expansion and rewritten
checking after explicitly proving descriptor fields unchanged and rewriting the
existing separation facts at the loop fold and final state fold. C and all
contracts remain unchanged; no kernel rule was relaxed. Whole-project checking
now reaches `could not evaluate held instance native carrier body`. Retained
session construction repeats that whole-project failure before a retained
recheck starts; this is not evidence of a fresh/retained disagreement for the
selected allocation proof. Keep the complete checkpoint at **51/52** until the
original whole arena project passes.


The carrier refusal reduces to a four-line C program preserving a held region
resource whose unrelated backing range uses a nested descriptor read. The
identified upstream baseline passes it; recovery `03abdc37d` fails while eagerly
evaluating the second body clause for an already-readable record carrier.
The repair first checks the same native promises in the selected scratch
evaluation and projects the immediate body only if a carrier needs that
authority. It skips no native check and changes no C compatibility boundary.
All eight native-record controls and the new
`held_record_input_preserves_opaque_body` fixture pass. Whole arena checking
now reaches `arena_free.contract` tactic 29 (`give` cannot find the owned
element), with a focused trace captured. The original allocation proof's fresh,
expanded and rewritten checks pass; retained session construction still awaits
the complete project. Keep the full-audit count at **51/52**.


The `give` investigation confirms that replacing its legacy memory consumption
with `without_fact_incrementally` does not repair the original arena-free
obligation. That candidate was reverted. The recovery source is clean at
`b5e26dcf6`; its complete-audit checkpoint remains **51/52**. Continue from the
focused `arena_free.contract` tactic-29 trace rather than inferring that an API
substitution solves the missing ownership match.


The complete `release_run` loop reduction now passes upstream baseline
`64f0f0d46` and fails recovery at tactic 14 (`give`), while the single-store
control without a loop passes recovery. The reduction is preserved in
`bugs/archive-iterated-give-loses-loop-descriptor-ownership.md`. PR #1205
publishes it alongside the opaque-carrier compatibility fixture; auto-merge
is enabled. The fixture passes fresh current upstream `ea081fe39` using a
build without debug information. No full-audit count changes.


The `give` coverage probe finds a real held range with equal base, proved lower
and upper bounds, and successful direct coverage; consumption nevertheless
misses it. The repair consumes the element in the already-selected iterated
clause's coordinates after selection has established the query's base and
exact shape, using the indexed resource operation. Guard, hole, width and
quantity checks remain intact; no ambient alias is published.

All seven active iterated-ownership controls pass (one ignored), including
existing four-size flat-work checks. Round-trip controls also check consumption
of the separate element and rejection of a repeated give. The complete
`iterated_give_preserves_descriptor_loop_ownership` fixture passes, including
fresh, expanded, rewritten and retained checking. Its later fold uses explicit
unchanged-descriptor and separation facts, just as the allocation proof does.
The original `arena_free` now passes `give` and reaches tactic 35's window fold;
that whole-project work remains open, so retain **51/52**.


The original arena-free loop window fold now succeeds with explicit unchanged
descriptor fields and separation transfer. The remaining final arena-state
fold needs its separation premises carried across the final live-count store.
An automatic attempt to recover the unchanged data field, both before and
after closing the cell resource, exhausts the existing bounded smart budget.
Those unsuccessful final-fold experiments were removed; the nine-line loop
window proof is retained. The next investigation should use the existing
`cleared` mark and the specific final store, without raising search limits.
The whole-project audit has not been rerun and remains last measured at 51/52.


Arena-free recovery now passes selected verification, expansion and rewritten
verification. Explicit transport of unchanged descriptor reads replaces the
exhausted automatic search; explicit rewrites transfer the three separation
premises, and a quantified transport closes the final postcondition through
the region descriptor. C, contracts and budgets remain unchanged.

A complete normal example audit still passes **51/52**, in 134.89 seconds
while a separate proof-mode check was running. Arena now advances past
allocation and free to `arena_write.contract` tactic 12: indexing the stored
data pointer rejects as leaving its pointed-to object. Its trace shows the
subrange authority and scalar index bounds are available; the retained storage
allocation is still inside `arena_initialized_storage`. Investigate that
allocation/domain boundary next. Retained-session construction requires this
whole project to pass, so no retained-mode success is claimed for arena-free.


The next failure is preserved as a
[complete isolated pointer-field write reproduction](../bugs/archive-c-pointer-field-write-loses-domain.md).
Its unchanged C and 146-line resource/proof file pass baseline `64f0f0d46` and
fail recovery at the same pointer arithmetic. Explicitly exposing the allocation
does not repair it; that experiment was removed. Arena-free passes fresh,
expanded and rewritten checks; retained-session creation stops at this later
arena-write failure, consistent with the whole-project audit. No proof-mode
disagreement or new design decision is claimed.


The next recovery increment separates an exact original symbolic C pointer
read from a native referent designation. Its C geometry route preserves the
complete read identity but grants no native place, extent, initialization or
access authority; NativeObjectOnly inputs and native-place queries remain
strict. Full typed pointer reads retain their immutable defining read before
cell enrollment, while already-known stored values are not relabeled as reads.
C pointer-value lifetime checks remain at the existing value-use boundary,
not duplicated in geometry classification.

All 34 pointer-domain controls pass, including partial/integer writes, havoc,
native refusal, exact retired-value rejection at value use and four-size
unrelated-retirement scaling (25 work units at every size). A broader selected
set of 160 read, store, designation, native-span and record controls passes.
This advances the complete isolated arena-write proof past its C store. The
original example remains unchanged at this checkpoint; explicit descriptor
frames and separation transfers have been checked in the isolated proof,
with the final unchanged-occupancy postcondition still under investigation.
The last full example audit remains 51/52; no activation or full green verdict
is claimed. All temporary diagnostic probes have been removed.


The final occupancy transport exposed a separate simple-checker defect:
quantified equality matching tried every unrelated target scalar as an array
index and exhausted 750,000 work units. A candidate limits equality
instantiation to matching bound occurrences, retaining scalar candidates for
intermediate order proofs. All 91 selected quantifier, frame, transport and
expansion controls pass, including the existing same-named-binder order case
and new matching-cell/read-kind and three-size unrelated-scalar controls.
The isolated transport now reports a bounded missing-frame refusal instead of
exhausting work. This is not a completed arena proof; the resource-held
occupancy read still needs its entry/store frame justified. No full-audit count
or activation status changes.


PR #1227 merged as `a536608ec`; its sole pushed commit `25e111dc3` is verified
as an upstream ancestor. The recovery observation repair now names fields of an
unfolded complete-object resource through the existing input-cell producer.
Previously it recorded scalar input naming as a program store at `region->start`.
The checked history also recognizes byte-preserving full-pointer observations
from a byte-identical source; actual partial writes, changed sources and Boolean
normalization remain rejection controls. This pointer-specific law depends on
the archive's full-width pointer-read representation and belongs with that
foundation, rather than being activated independently on the older upstream
pointer representation.

Two focused recovery selections pass: 170 observation/quantifier/byte/pointer
controls and 213 initialization/read/store/native-place controls. The latter
exposed an outdated negative expectation already failing at `48a09a658`:
ordinary C byte-span writes verify through the C allocated-access route.
The corrected control verifies that program and rejects an added `valid_place`
postcondition; it preserves the independent native-geometry boundary.

The complete staged arena-write reduction now checks its occupancy transport.
An explicit rewrite of the already-proved capacity equality closes the final
quantified goal, but checked return-fold certification rejects an unjustified
path fact. The identical complete proof passes baseline `64f0f0d46`. Stop proof
variations and identify that rejected fact next. The original arena-write proof
remains unchanged; the last full audit is still **51/52**, with no activation
or full green gate claimed. Temporary probes are removed from this checkpoint.


The checked return-fold defect is repaired at its two producers. A checked
post-return transport now records its exact completed proposition in the
execution certificate. A post-return `have` scope starts from the facts that
preceded selected materialization, retaining newly derived facts as checked
successors rather than assuming them in its root. No arbitrary return facts
are authorized. The complete original arena-write C, resources and contracts
are preserved; its proof now states the relevant descriptor frames explicitly.

The isolated complete arena-write proof passes fresh, expansion, rewritten and
retained checking. The quantified and reduced return-fold Markdown fixtures
pass, along with 368 selected outcome, scope, transport, initialization and
native-place controls. The complete normal example audit is **50/52**, not the
previous checkpoint's 51/52: arena advances to destroy after its first free,
and binary-tree fails folding the swapped child resources. The tree failure
also reproduces at `48a09a658`, before the observation and return-fold repairs.
Both compatibility failures remain prerequisites to foundation activation;
this checkpoint is not a full green gate or completed shared object model.


PR #1231 extracts the return-proof repairs against upstream `60c97316a`, with
auto-merge requested. Its 1,048 selected unit controls (including the whole
scaling suite) and complete original-source Markdown fixture pass.

The next recovery checkpoint repairs two compatibility cases without changing
C or contracts. Proven null pointer values have no referent designation, so
resource matching can exchange their read spellings; numeric equality of
non-null pointers still cannot supply a designation. Binary-tree passes its
original proof and fresh, expansion, rewritten and retained checking.

Storage retirement now compares the selected checked byte footprints rather
than requiring identical element widths. A stated element range must be
forward and nonwrapping before it can preserve a separate input object across
retirement. The original arena-destroy proof passes, with missing-bound and
shorter-range rejection controls. All 376 selected pointer, lifetime, heap,
native-place and output-initialization controls pass, including three-size null
matching with unrelated pointer equations. Temporary private probes are removed.

The complete normal example audit is now **51/52**. Arena advances through
write, read and destroy to its pipeline caller: matching `arena_state(arena)`
against `arena_state(first->arena)` fails at the first `arena_free(first)` call
on the allocation-failure branch for the second region. The trace proves
address equality, which alone does not establish full pointer identity. The
original arena-write proof passes fresh, expansion and rewritten checking;
whole-project retained construction stops at that pipeline mismatch. Do not
claim full arena retained success, foundation activation or a full green gate.


PR #1231 merged as `962429a54`; both pushed commits `b7c864aa9` and `bc74e9c8e`
are verified upstream ancestors. Its CI failure was the retired-terminology
documentation check, corrected without changing proof behavior. The failing
CI shard's 968 library tests pass locally; its importer controls also pass
with the pinned exporter and LLVM environment.

The recovery checkpoint's unchanged pinned decoder passes its exact word,
span and backing claims, helper/decoder expansion, rewritten checks and retained
outer-probe checks in 20.985 seconds under the normal limit. An earlier run
timed out at 30 seconds while other proof/import work was running; the idle
recheck used the same limits and no implementation changes.

Explicit checked resource-body transfer gets the pipeline past its first free,
but the reverse transfer exposes a
[reproduced simple-checker budget defect](../bugs/post-call-range-separation-exhausts-simple-checker.md).
The profiler attributes the exhausted work to indexed goal equality rewriting
and selected premise reduction for the separation goal. Stop local proof
variations and reduce that comparison. The failed experimental proof is not
installed in the original example. The full audit remains **51/52**.


A direct kernel control confirms that full-width pointer-address reads survive
a numeric storage alias, input observation and a recorded read projection.
`pointer_address_reads_survive_observation_through_a_numeric_storage_alias`
passes, so those ingredients alone do not reduce the pipeline failure. The
smaller two-call C experiment stops at an earlier native-span fold and is not
a reproduction. Keep the complete original-source pipeline and its profile
as the defect witness while inspecting the exact read endpoints. No new
semantic law or broader alias permission has been introduced.


The broader restored-baseline audit passes **1,360/1,364** selected pointer,
load, scope, native and scaling controls. Two failures are known origin
rejection gaps: the const pointer-field countermodel and the branch-interface
address-only child. A complete caller now confirms the
[P1 scalar-subobject origin defect](../bugs/pointer-arithmetic-crosses-scalar-subobject.md):
it stores `&pair->first + 1` and verifies a helper dereference at the sibling's
equal address. This defect was already recorded on earlier recovery
checkpoints; it is not attributed to the discarded constructor experiment.
The other failures are the existing modular record-identity return and an
indexed-load expansion expectation. The 51/52 example result is therefore
insufficient for activation, even after the arena pipeline is repaired.

The attempted ordinary/cached pointer-constructor unification passed its new
producer check but failed 15 broad controls and regressed three additional
example projects. It is fully reverted and its extra test removed; the
restored tree has no private probes or candidate source changes. A typed
read-graph entry must not turn an address observation into origin evidence.
The next priority is the demonstrated origin defect, followed by the pending
resource-transfer/checker-budget repair. The decoder and three selected pinned
profile boundary controls passed on the committed recovery model.
