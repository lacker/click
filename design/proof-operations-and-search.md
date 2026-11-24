# Separate proof operations from proof search

Status: proof/search split, explicit proof driver, and shared implicit/explicit solver implemented.
The next step is to remove the inventoried operation-to-search dependencies
one at a time. The general fast-operation guarantee is not established yet.

## Design check

- **Parts:** proof operations, discovery, proof-script driver, persistent state.
- **Boundary:** explicit operations remain on `kernel::proof::ProofObject` and
  its Surface `Proof` wrapper; discovery is exposed through `kernel::search::ProofSearch`.
- **Cost:** the interface split preserves operation costs. The shared solver
  includes the former implicit zero-witness attempt, entry-witness transport,
  and return-resource folding;
  these remain expandable search, with existing budgets.
  The eventual operation bound is selected input and necessary state delta,
  up to indexing factors; ambient buckets and history are not explicit input.
- **Result:** search uses the existing operations and persistent successors.
  There is no second proof state, proof conversion or new validation pass.
- **Lowering/refusal:** syntax and obligation generation are unchanged.
  An omitted obligation proof and written `close()` use the same strategies;
  explicit solve can now prove the former implicit-only zero-witness case.

## Implemented split

`ProofObject` remains the authority for semantic successors. `ProofSearch<P>`
is a stateless associated-function interface over an existing context `P`.
For example, `ProofSearch::derive_proposition(&facts, &goal)` searches over
kernel facts, while a Surface specialization can use the same interface to
select and spell a sequence of source proof operations. There is no new
runtime session, allocation, copied proof or permission check.

Both interfaces belong to the kernel. Implementation placement follows the
inputs each method needs:

- `kernel/search/proposition_search.rs`: semantic proposition discovery,
  formerly a trait supplied by Surface planning.
- `kernel/search/permission.rs`: the existing enumeration capability, with
  its existing construction semantics unchanged.
- `kernel/**/legacy_search.rs`: extracted traversals beside the private state
  they inspect. Existing entry points forward to `ProofSearch` unchanged.
- `surface/proof/**/search.rs`: discovery that needs Click source terms,
  spelling or expansion records, implemented on `ProofSearch<Proof<'a>>`.
- `surface/planning/solve.rs`: existing certificate planning support.

The explicit Surface `Proof` interface no longer owns the extracted discovery
methods. Its remaining calls to search are visible in the dependency inventory.
`ProofScope` search forwarding adapters now belong to `ProofDriver<ProofScope>`. Direct helpers such as indexed fact lookup and
retrieving the retained spelling map stay outside the search interface.

The existing `PropositionDerivation` representation and its checking lifecycle
are unchanged. Moving its discovery code does not endorse producer/checker
revalidation as a design for new operations.

## Driver and obligations

`surface::proof::driver::ProofDriver` borrows a `Proof` or `ProofScope`. It
interprets source proof steps, nested scripts, theorem applications and closure
bodies, choosing explicit operations or `ProofSearch` at each frontier. This
is one interpreter, not separate fast and slow passes. `proof.driver()` borrows
the existing persistent state without allocating or copying it.

The implementations live in `surface/proof/driver/`. Existing helper modules
mount those files as private child modules to retain helper visibility. Claims
and execution orchestration are also housed there, with their existing logical
module names preserved. The kernel's semantic `ProofObject` and `ProofSearch`
remain kernel interfaces; this source interpreter belongs in Surface because
it consumes parsed Click proofs, source locations and expansion records.

For statement obligations:

1. `Proof::prepare_step` runs the existing operation under its obligation probe,
   returning the existing conditional candidate and recorded requirements.
2. The driver proves those requirements at the original frontier, using the
   supplied `by`/`requires` blocks or implicit search when no block was written.
3. `Proof::finish_prepared_step` publishes the retained candidate after the
   requirements are proved. It never reruns the primitive. Failed preparation
   is a final refusal; the candidate cannot prove its own inputs.

Obligation generation is intended to be fast; implicit solving is legitimately
slow and expandable. An omitted obligation proof invokes the same
`ProofSearch::try_solve_closure` entry point as written `close()`. The driver
provides no private witness heuristic, extra premise list or caller-requirement
shortcut. Such strategies belong in the shared solver. The implicit tail
schedules the remaining C and outstanding goals; it is not another solver.
Step preparation retains emitted prerequisites even when already known,
and fold body facts use the same obligation driver. The driver handles every
unwritten slot through ordinary solve. The raw fold operation no longer
re-enters the driver. Named, population/authority, operational wrapper and
legacy outcome folds retain their result through obligation proofs, including
post-return folds. Completion uses retained path endpoints, not backward history
recovery or a speculative whole-path certification probe. Arithmetic evaluator
obligation generation remains a separate migration.

## Dependency inventory and enforcement

[`build_support/proof_search_edges.tsv`](../build_support/proof_search_edges.tsv)
is the frozen production reference inventory. Columns are source path, caller
role, owner/function, search or driver target and number of references. Repeated calls
from one function to one target share a record. It is a lexical reference
inventory, not a type-resolved or transitive Rust call graph.

Roles distinguish the work remaining:

| Role | Meaning |
| --- | --- |
| `legacy-bridge` | Preserved kernel forwarding boundaries into extracted traversals. |
| `legacy-caller` | Kernel dependencies on those old entry points; these expose propagation beyond those bridges. |
| `operation` | Source operation, transport, validation or transition construction still calls discovery. |
| `driver` | Explicit proof interpretation, including legitimate implicit obligation solving. |
| `operation-to-driver` | Remaining proof-operation calls into orchestration; inspect their transitive behavior. |
| `dispatch` | Source drivers explicitly select a smart tactic or implicit closing. |
| `presentation` | Spelling and trace helpers depend on discovery helpers. Audit independently of semantic steps. |
| `search` | Calls made within the extracted search interface or planning modules. |
| `mixed` | Drivers and auxiliary planners; semantic roles are recorded in the caller audit. |
| `import` | Named import, not a runtime invocation. |

The current inventory contains 662 records: 4 legacy bridges, 17 kernel callers,
6 Surface operation dependencies, 0 operation-to-driver dependencies,
122 driver records, 6 presentation records,
489 search-internal records, 16 mixed records and 2 imports. These are reference
records, not individual invocation counts or independent performance defects.

Do not add all these rows and call the result a count of slow bugs. Several
callers reach the same traversal; dispatch and search-to-search calls are
expected. The `operation`, `operation-to-driver` and legacy rows are the migration list;
`mixed` rows have caller-level roles in the linked audit; classification does
not certify their callees as fast. One operation record belongs to theorem application implemented
on `ProofDriver`: moving dispatch must not hide those search dependencies or
reclassify them as legitimate implicit solving. Driver placement alone is not
an efficiency guarantee. Named theorem applications now use retained preparation,
driver-solved obligations and publication in pure, fixed-state, live and returned
contexts. The remaining selector edge covers unsupported outcome dispatch. The three migrated primitives have test-build
no-discovery scopes; every `ProofSearch` entry records discovery before work,
even when called from another search. Generic applications instantiate checked
statements without re-running declaration proofs; no guard exception remains.
See the theorem boundary section in the
[efficiency contract](../docs/internals/verification-efficiency.md).

The search inventory includes these kernel bridges:

| Existing entry point | `ProofSearch` implementation | Ambient work to resolve |
| --- | --- | --- |
| `memory_range_aliases` | `borrow_aliases` | Pointer aliases used by borrow queries. |
| `permits_memory_access_with_assumptions` | `borrow_access` | Legacy write check exercised by tests. |
| `owned_validity_candidates` | `ownership_validity_candidates` | Candidate owners for composition validity. |
| `call_kept_ownership` | `call_frame` | Residual caller resources and composite families. |

`build_support/proof_search_boundary.rs`, invoked by the normal build boundary
check, rejects new references to the registered search entry points and new
unclassified `ProofSearch` methods. It also rejects returning a registered
search method to `Proof`. It also registers the driver methods, rejects moving
them back to `Proof`/`ProofScope`, and inventories `.driver()` acquisition so
new operation-to-driver dependencies require explicit review. Tests pin the exact inventory, including deletions,
and exercise direct calls, function references, type aliases and macro tokens.
Changing the inventory is a reviewable architecture change, not an automatic
regeneration to make the build pass.

This source guard does not establish complexity. It cannot discover a new
inline loop, resolve arbitrary macro-generated calls, or prove an arbitrary
helper fast. The existing operation audit and scaling tests remain necessary.
The separate target list includes compatibility entry points so a caller cannot
hide an existing search merely by using the old wrapper.

## Have prerequisite boundary

`Proof::begin_have` opens a nested goal or reports ordinary lowering
requirements; it does not acquire a driver or schedule their proofs.
`ProofDriver::open_have` (and its source-proof adapters) owns the existing
lowering-obligation probe, invokes the shared obligation solver when needed,
and opens the scope with the resulting facts. Strict replay takes the direct
operation path. No new obligation format or proof rechecker is introduced.
This lowering adapter still probes and invokes `begin_have` again after proving
its lowering requirements. It is separate from the removed step/fold completion
retry. Its cost and the separation-observation setup costs need their own bounds;
the existence of a second invocation alone does not demonstrate bad scaling.

The source boundary rejects driver and registered search references inside
`begin_have`. The primitive regression leaves implicit solving enabled and
requires raw opening to report a prerequisite; driver opening succeeds and
retains the prerequisite proof. Scoped-conversion expansion replays with
implicit solving disabled. The operation-to-driver inventory is now empty.

## Contract-claim prerequisite boundary

`Proof::begin_contract_claim` opens an already-lowered claim or reports its
missing definedness obligations through the ordinary obligation channel.
`ProofDriver::open_contract_claim` imports the claim's lowering facts and
schedules prerequisite proofs. Its `open_contract_claim_without_lowering_facts`
adapter uses the existing facts instead. Both retain prerequisite certificates
before the claim's own steps, preserving expansion and strict replay.
The source guard prohibits direct driver/search references in the primitive.
Claim lowering, goal transformations, and state preparation are unchanged.

## Resource-scope completion boundary

`ProofScope::join` closes directly or reports the missing resource-body fact
through the ordinary obligation channel. It cannot call the driver or search.
`ProofDriver::complete_scope` runs the ordinary implicit solver through
`close_scope_with_body_fact_proof`. Expansion retains each resulting proof
as a `have` at the end of the scope. Nested opens use `complete_nested_scope`
before incorporating the direct checked successor. Function-exit closes use
the deferred driver route and attach the same in-block facts at the outcome.

## Branch interpretation boundary

`ProofDriver::apply_execution_if_within`, `apply_execution_branch_within`, and
`apply_focused_expanded_execution_arm` interpret arm scripts between the existing
proof-object split, focus and join operations. `apply_expanded_execution_if` is
also a driver entry point, including inside resource scopes. The former
`Proof::apply_execution_if_with` callback API is removed: proof-level cases now
use the same explicit split/focus/drive/join sequence in the driver. C-branch
entry checks, infeasible-arm refusals, parent continuations and terminal joins
retain their existing rules and exact checked histories. There is no second
checker or rebuilt proof state.

## Detailed caller classification

The [caller audit](proof-boundary-classification.md) classifies the current 16 mixed and
0 operation-to-driver records by why they invoke search or interpretation.
It distinguishes expected dispatch from hidden obligation callbacks, declaration
validation and the remaining primitive search dependencies.
The proposed enforcement changes are for design review; no behavior changes or
new scaling measurements accompany that classification.

## Next step

For each operation dependency: reproduce its ambient cost with a red scaling
test, discuss the explicit rule or indexed representation, then replace the
search and repair proofs. Preserve the C program, contracts and safety refusals.
Remove the corresponding inventory records as the dependency disappears.
Start with loan permission through an actual write, separating alias growth
from symbolic-loan growth; the [operation audit](../docs/internals/verification-efficiency.md#operation-audit-ledger)
retains the other candidates and coverage gaps.

The intended end condition remains: an expanded proof executes through proof
operations without accessing `ProofSearch` or a legacy slow operation. This
refactor deliberately adds no strict runtime mode and does not claim that end
condition. Session capabilities, stricter state views and expansion enforcement
can be designed when needed; they are not prerequisites of this initial split.
