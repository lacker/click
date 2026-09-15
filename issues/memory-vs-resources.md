# P1: Unify memory and other resources across contracts and callbacks

## Objective and violated invariant

Memory is a primitive resource family inside the general resource system.
Contracts, resource transfer, framing, observation, and callback application
must use that system consistently. Packaging memory in a declared resource
must not break an otherwise expressible contract merely because different
implementation paths evaluate its ownership, dependent addresses, or effects.
Explicit fold/unfold steps may still be necessary to cross an abstraction.

This is a language-preserving implementation project, requested on
2026-09-11 and rebaselined on 2026-09-14 after the stable-views campaign
([the stable views record](../docs/internals/stable-views.md)) shipped a
different frame model from the one this plan's later chunks assumed. It
covers internal refactorings and existing-semantics bug fixes, not new
resource capabilities. The rbtree augmentation callbacks
([rbtree-example.md](rbtree-example.md), C6) wait on it.

Success means one checked account of a contract's resource transition, with
memory-specific behavior supplied by the memory family and its effect
projection. Merely renaming enums, adding a common wrapper around divergent
implementations, or making one callback fixture pass is insufficient.

## Status at the rebaseline (origin/master `dc6bb690`, 2026-09-14)

The W0 to W5 chunk handoffs that used to fill this file are in the git
history of this path; they are summarized here by outcome only.

| Chunk | Outcome | Where it lives now |
| --- | --- | --- |
| W0 baseline | Done. G1 fixed upstream (`16fe83e4`), G2 (`7e55fdc7`) and G3 (W3) fixed. | `rb_augment_callbacks_helper_owns*.md`, `contract_owns_through_composite_field*.md` |
| W1 normalized resource specification | Done. `CResourceSpec` carries a `CResourceTerm` plus explicit access, quantity, transfer role, and snapshot; families validate their own combinations. | `src/kernel/primitives.rs`, `resource_lowering.rs` |
| W2 body-independent contract interface | Done. `CFunctionContractInterface` serves verified functions, external assumptions, named callbacks, and execution theorems; evidence kinds stay distinct. | `src/kernel/primitives/contracts.rs`, `callback_contract_tests.rs` |
| W3 dependent entry clauses | Done. One kernel evaluator for direct and named contracts, checked load/guard obligations, event-driven waiter worklist with interval and symbolic fallbacks. | `contract_*composite_argument*.md`, `contract_nested_*`, kernel worklist tests |
| W4 authoritative effect projection | Done. One `CFunctionResourceTransfer` per application; `project_contract_memory_effects` feeds havoc, refinement, loops, storage checks, and certification. | `authoritative_memory_projection_*` tests |
| W5 observation provenance | Partial. Support-occurrence provenance, memory-dependent projection footprints with load prerequisites, scoped-open and callback mutation regressions landed (checkpoints A to E1). The E2 "expanded leaf footprint index" design was investigated, rejected, and is now retired by this rebaseline (see D1). | `rb_augment_callbacks_helper_{mutates_body,rejects_changed_cell,consumes_suite}.md`, `resource_scope_*.md`, `invalidate_memory_support` |
| W6 binder transport | Half done upstream. `570ac8a0` replaced the field-free `ResourceField` rename sentinel with `ContractSubstitutions` and `InstanceRename`; the parser-side call-binder registry was reviewed and kept, with the reason recorded in that commit. | `src/surface/lowering/contract_substitution.rs`, `CCallBinderTransport` |
| W7 qualification and cleanup | Not started. | |

### What the stable-views campaign changed under this plan

- **The frame model is a partition, not an expansion.** A valid context is a
  partition: distinct owned occurrences are bytewise disjoint at every depth,
  composites included, and the kernel does not reason inside a folded
  composite beyond its one-level frontier. `4b9debcd` decides a call's
  effect/view separation by occurrence provenance first and consults
  arithmetic only for a partial borrow of one occurrence. The E2 handoff's
  required representation, a per-composition footprint of every recursively
  expanded owned leaf posted into an interval index, contradicts that rule
  and must not be built.
- **Loans carry what W5 was reaching for.** Observations keep their loan
  identity through projection, fold, unfold, `open`, `close`, normalization,
  range splitting, and callback-fact extraction; produced composite bodies
  are checked against what the caller holds across the call; every
  allocation-retiring path consults the ledger; return validates
  obligations before recovery. A fold whose fact-bearing body views memory
  its own context owns is refused (`dc6bb690`).
- **`views` is now a stable loan and escaping borrows exist.** A folded
  composite may hold the loan it packages; the language-preservation
  contract below is rewritten against that meaning.
- **A second transition route appeared.** `prepare_contract_resource_transfer`
  in `src/kernel/functions.rs` branches on `plan_stable_views`: a call site
  plans loans, while the verified-body path executors, the contract
  entry-state builder, and certification's transition applier consume their
  requirements definitionally. The fix-views close-out flagged that route
  for review; it is this issue's D2.
- **The ambient composition expansion the E2 investigation blamed is still
  present.** `frame_expanded_compositions` in
  `src/kernel/assumptions/memory_reasoning.rs` expands every owned
  composite of every composition (memoized by storage pointer) and is
  consulted by the memory DAG's call-havoc, loop-havoc, and effect-frame
  hops in `src/kernel/memory_provenance.rs` when direct evidence cannot
  separate a loaded pointer from the havoc ranges. This is the path behind
  the recorded `owned-vector` budget exhaustion. It is D1.
- **Stale cross-references.** The old plan cited `function-contracts.md`,
  deleted on 2026-09-11 when that campaign closed; its callback residue is
  this issue. `rb_augment_callbacks_const_suite.md` now expects `pass`
  under the default semantics.

## Language-preservation contract

Every worker must preserve the following. A proposal that needs a different
rule is outside this issue and must be reported, not silently included.

1. Keep existing Click syntax, resource declarations, tactic forms, and C
   source unchanged. Fixing a verifier bug may make an existing valid
   contract verify; strengthening regression sidecars to exercise real
   footprints is allowed. Do not rewrite C to accommodate the verifier.
2. `views` is a stable, read-only loan for its scope, as defined in
   [the stable views record](../docs/internals/stable-views.md). A call-scoped
   view is lent and recovered; it does not mint a persistent caller view.
   An escaping borrow is a folded composite holding the loan it packages,
   released when the composite is consumed. Ownership is never recovered by
   entailment, normalization, fold, or theorem.
3. `owns` returns the resource selected at entry. Changing a pointer field
   does not retarget a borrowed memory range at return. Exclusive instances
   retain their identity and acquire post-call fields constrained only by
   guarantees; ownership alone does not freeze fields.
4. `consumes` transfers owned authority without an implicit return;
   `produces` describes returned authority at the appropriate post-state,
   including contracts indexed by `result`. Produced ownership is not proof
   of allocation freshness.
5. Memory range splitting, token/composite quantities, instance exclusivity,
   allocation authority, guarded recursion, and existing population rules
   remain distinct family semantics. A common representation does not make
   every operation valid for every family.
6. Loads and stores still require appropriate authority, with existing local
   and read-only storage rules. Owning a wrapper must not expose its body
   for arbitrary proof steps without the currently required fold, unfold,
   `open`, or observation. Internal effect queries are not public unfolding.
7. All finite writes stay within the checked effect footprint, even on paths
   that do not return. Memory outside the footprint is preserved only with
   checked frame evidence, including address dependencies for dependent
   loads. Failure to prove overlap is not disjointness.
8. Automatic callback formation remains bounded and exact; explicit execution
   theorems remain the escape hatch. Do not broaden smart search or weaken
   refinement checks to hide a representation problem.
9. Preserve source-level expansion, checked proof provenance, independent
   contract certification, and the no-body-rerun ratchet. Pending or failed
   obligations must never become successful authority through a cache.

Explicitly excluded: views of field-bearing instances; new memory instance
binders or proof parameters; a new `memory(...)` spelling; selectable
resource capability syntax; fractional permissions; dynamic footprints for
counted populations; new recursion forms; more permissive binder inference;
the loan-preserving havoc's known cells-times-symbolic-loans cost (pinned in
the stable views record); and unrelated prover completeness work.

## Design decisions

Settled by the user on 2026-09-14: the first option of each decision below
is the chosen one. The alternatives are kept so a worker knows what was
rejected and why.

**D1. Load framing across havoc for cells inside composites.** The memory
DAG justifies a load surviving a call or loop havoc when the loaded pointer
is proven disjoint from the havoc's mutable ranges. When the pointer's cell
is owned only through a composite, the direct prover cannot see it, and the
frame path expands every composition. Options:

- *Provenance first (chosen).* Mirror `4b9debcd`: every havoc range
  already records the owned occurrence it was reserved from. A pointer whose
  authority comes from an occurrence the call did not reserve is disjoint
  by the partition invariant; only the same-occurrence case needs arithmetic,
  and that arithmetic works on the one-level frontier, not a recursive
  expansion. Where the owning occurrence is unknown, the hop fails closed and
  the user bridges it with `observe`/`unfold`, as law 8 of the stable views
  record already requires elsewhere. Risk: corpus proofs that leaned on the
  expansion; the corpus run in W5' measures this before any code moves.
- *Bounded indexed expansion.* Keep the expansion but index it by the
  composition that owns the pointer and bound its depth. This is the E2
  direction in a smaller form; it still reasons below the one-level frontier
  and needs the cold/warm matrix E2 specified.

**D2. The definitional transition route.** The call-site route plans loans;
the four reconstruction callers consume requirements definitionally so a
state rebuilt around an application that already happened does not lend
twice. (Implemented under W7' below; the audit found no site holding a
call's transfer record, so the typed purpose and the agreement test are
the whole of it.) Options:

- *Rebuild from the record (chosen).* Where a checked
  `CFunctionResourceTransfer` exists for the application (certification's
  transition applier, the entry-state builder given a selected interface),
  rebuild from that record instead of re-consuming; where none exists (a
  function's own entry state), keep the definitional consumption as the
  entry assumption and name it so with a typed purpose instead of a boolean.
  Pin that the call-site and reconstruction routes produce the same
  resource state for one interface.
- *Keep both and document.* Accept two consumption semantics as two
  purposes and only replace the boolean with a typed purpose. Cheaper, but
  "one checked account" then has a documented exception.

**D3. Binder transport versus instance renaming.** After `570ac8a0`, an
execution theorem's `as` map is a rename of spellings applied while lowering
clauses, and a call's `{ binder: instance }` map is an identity transport
carried on the selected interface. W6 asked to keep spelling separate from
semantic identity, which is what this split does. Chosen: treat W6's
remaining scope as an audit that the three forms (direct call, named
contract, execution theorem) reach the same kernel identity map with the same
ambiguity refusals, and add the missing agreement test; do not merge the two
mechanisms.

## Remaining work

Default order is W5' then W6' then W7'. Each chunk is one worker in a
dedicated worktree, delivering coherent green commits; the shared files
(`src/kernel/functions.rs`, the primitive types, surface lowering) are never
edited by two workers concurrently.

### W5' — Rebaseline frame provenance on the partition invariant

D1 is settled: provenance first.

**D1 landed 2026-09-14** (`Frame loads across havoc through the one-level
composite frontier`, base `083ebcf8`). Measurement first: with the
recursive expansion disabled outright, 1 of 1,520 mdtests failed
(`call_havoc_keeps_names_by_ownership.md`, depth one) and all 27 examples
passed, `owned-vector` within budget; the frame path fell through 13,218
times without any other proof noticing. The frame check now opens each
owned composite of a published composition one level
(`expand_owned_composite_resource_facts_one_level`,
`frame_frontier_compositions`); nested composites stay folded and a cell
below the frontier is refused. Regressions:
`frame_check_opens_owned_composites_one_level_and_charges_per_head`
(frontier framed, nested refused, work constant over depths 1, 2, 4, 8) and
`mdtests/rb_augment_callbacks_helper_rejects_call_after_close.md` (R3:
permitted mutation inside one open, close, next callback call refused for
the missing view of the callback cell). Gate: unfiltered `scripts/check.sh`
exit 0. The walk over the published compositions is retained and bounded
by the proof's own compositions (11 at most in the corpus); it is not a
project-wide scan. A depth-two mdtest was attempted and dropped: the
natural proof failed under the old recursive expansion too, and the
unfolded spellings hit the two findings below, so the nesting rule is
pinned at the kernel level.

Findings from this chunk:

- Fixed 2026-09-14 (`Close an open of a viewed composite the same way
  from a step as from execute`): `open(viewed composite) { step(); ... }`
  refused the close with `the rewritten composite is absent from both
  resource representations` while `open { execute(); }` passed. The
  mid-body close in `proof_object/scope.rs` re-lowered the `open(...)`
  clause, which spells no access, as an owned head; the deferred close at
  function exit folds against the state and never did. The close now
  records the head as the closed state holds it. Regressions:
  `rb_augment_callbacks_helper_mutates_body_stepwise.md` (the reduction,
  passes) and `rb_augment_callbacks_helper_calls_after_close_through_view.md`
  (the viewed spelling of the close case: the call after the close is
  authorized through the caller's stable view, the matched positive to the
  owned refusal).
- Reported, not filed: after `execute()` reaches the outcome state, `unfold(tree(r))` followed
  by `unfold(leaf_cell(r->leaf))` fails to lower the nested argument
  (`missing pure fact: loadable(base=r, bytes=8)`), although the same two
  unfolds lower before `execute()` (`c_chained_field_access.md`).

Classification of the remaining W5 semantic cases:

- Mutation then scoped-open expiry: pinned in both spellings, the owned
  refusal and the viewed continuation.
- Fresh ensures after invalidation: the verified call path builds the post
  state from the havoc memory through the state's memory hook before the
  return outputs are installed (`functions.rs`, call havoc then
  `post_outputs`). Under the partition invariant a havoc range and a live
  residual support come from distinct occurrences, so the memory hook is
  defense in depth there; support consumption is pinned by
  `rb_augment_callbacks_helper_consumes_suite.md`. No further fixture.
- Nested and opaque composite prerequisite footprints: E1's
  `observed_projection_tracks_loaded_*_prerequisite` tests remain the
  coverage; opaque footprints stay conservative (`Unknown`).
- Support preservation through fold/unfold/open/close: the stable-views
  regression map rows for composites and escaping borrows.

W5' is complete; the unfold-after-execute lowering finding is reported
above and is outside its scope.

- Measure first (done, above).
- Implement D1's chosen option (done, above).
- Classify each remaining W5 semantic case as covered by an existing
  stable-view or callback regression, or add the one missing fixture:
  a permitted callback mutation followed by scoped-open expiry (the
  `mutates_body` and `resource_scope_*` fixtures cover the halves
  separately); fresh ensures inserted after a pre-return invalidation of
  old overlapping support, with disjoint observations surviving; nested and
  opaque composite prerequisite footprints; and exact support preservation
  and rejection on fold/unfold/open/close.
- Keep pure exact-pointer theorems (`Copy(augment->copy)` as a no-memory
  predicate) separate from composite-supported predicates; no callback-fact
  retention list and no `FactProvenance` sidecar.
- Scaling: a four-size deterministic curve for whatever query replaces the
  expansion, charged to the queried occurrence's frontier and edges, and a
  two-axis curve (calls versus unrelated compositions) only if an indexed
  expansion survives.

**Done:** R3 and R6 cases above are pinned; no memory-DAG hop scans the
composition set; `scripts/check.sh` passes.

### W6' — Binder audit

D3 is settled: audit only. Depends on W5'.

**Landed 2026-09-14** (`Bind a call's instance binders through one checked
kernel constructor`). Audit result: the three forms are two kernel
constructions feeding one engine. A direct call map
(`step(callee(...), { binder: instance })`) reaches
`selected_call_binder_application`; a named contract's proof arguments
(`step(Contract(instance, ...))`) reach the argument zip in
`execute_c_function_contracts_paths`; an execution theorem's `as` map only
renames spellings (`InstanceRename`), and its block binds through one of
those two steps. Both produce `ResourceCallApplication`, and the engine
checks completeness (every declared binder bound) for both. Before this
chunk the named construction also checked ownership and distinctness in
the kernel while the direct one trusted the surface and a later transfer
refusal, with a different message. Now both call
`ResourceCallApplication::bind`, which refuses an unowned instance and an
instance supplying two binders with one message set. The parser's
call-binder registry stays, documented at its definition
(`CalleeResourceBinder`), because call maps resolve while parsing.
Regressions: `direct_call_map_is_checked_in_kernel_like_named_proof_arguments`
beside the named-path kernel test, and four fixtures pinning the shared
and consumed-instance refusals in both forms
(`c_call_binder_transport_rejects_{shared,consumed}_instance.md`,
`c_named_contract_rejects_{shared,consumed}_instance.md`). Positive
agreement stays pinned by `c_call_binder_transport*.md` (direct) and
`c_contract_executes_counter_*.md` (theorem plus named): identity kept,
fields fresh, return snapshots unchanged. No lookup changed shape, so no
new curve.

- Audit that direct calls, named contracts, and execution theorems resolve
  binders to one kernel identity map (`CCallBinderTransport`) with the same
  exact/forced pairing and ambiguity refusals, and that expansion spells the
  user's binders without kernel identities.
- Add the agreement regression across the three forms for the counter and
  instance fixtures (`c_contract_executes_counter_*`,
  `c_named_contract_rejects_*`), and a multi-size binder curve if any lookup
  changed.
- Preserve fresh post fields, exclusive identity, and return snapshots.

**Done:** R5's instance half is pinned across the three forms; no parser
registry carries semantics the declaration metadata lacks, or the retained
one is documented at its definition.

### W7' — One account, cleanup, and documentation

D2 is settled: rebuild from the record. Depends on W5' and W6'.

- Implement D2 (done 2026-09-14, `Name the two purposes of a contract
  resource transition and pin their agreement`). The boolean is now
  `ResourceTransitionPurpose::{CallSite, FunctionBoundary}`. The audit of
  the four definitional callers (the two verified-body path executors, the
  contract entry-state builder, and the outcome-through-contract applier)
  found every one to be a whole-function judgment at the function's own
  boundary, so no call-site transfer record exists for any of them to be
  rebuilt from; the "rebuild from the record" half of D2 has no site. The
  proof executor's exit rule picks the purpose from whether the path lent
  at entry. Agreement is pinned by
  `call_site_and_function_boundary_transitions_agree_on_the_callee_entry`:
  for one interface with an owned range, a viewed range, and a consumed
  token, both routes check in the same requirements with the same roles,
  project the same effects, hand the callee the same authority, and leave
  the caller the same unrelated frame; they differ only in the lend. This
  closes the fix-views carry-over item about the definitional routes.
- Retire the surface footprint traversal (done 2026-09-14, `Derive every
  resource-derived write footprint in the kernel`). The traversal
  `collect_owned_resource_memory_segments` and the interface's
  `resource_derived_mutable_segments` are deleted. Its two consumers now
  read the kernel: a function's frame comes from `project_contract_memory_effects`
  as before, and a loop's declared frame is installed at loop entry by
  `install_declared_loop_frames` from the kernel's evaluation of the loop's
  own specs through the one shared derivation, `checked_owned_memory_ranges`.
  A resource-origin loop check (declared or inherited) without installed
  ranges fails closed; the segment list on such a check is never read. The
  "mixed" refusal now means an explicit effect segment beside a
  resource-derived frame, which no source can spell since the `mutable`
  clause was removed; the guard a derived segment used to carry for
  automatic refinement is read from the composite definitions instead
  (`requirements_reach_a_guarded_composite`). Regressions:
  `declared_loop_frame_is_installed_from_the_loop_specs_not_from_segments`,
  the existing loop fixtures (135 pass unchanged), and the retained
  no-fallback and mixed-frame kernel tests.
- Unify resource clause numbering (done 2026-09-15, `Number a refused
  resource clause by the clause the author wrote`). The premise was
  slightly off: the parser flattens an aggregate clause (an embedded struct
  field) into one requirement per segment, so the surface check and the
  kernel both counted flattened clauses and agreed with each other while
  disagreeing with the source; reproduced as "resource clause 5 of 5" for
  the second of two written clauses. The function block now records the
  source clause of every flattened requirement and ensure, and one helper
  turns that into source positions for the kernel's stamped clause
  provenance and the surface loadability check alike. Regressions:
  `contract_numbers_clauses_by_source_not_by_lowered_spec.md` and its named
  form.
- Run the R1 to R6 matrix (table below) across direct calls, named
  callbacks, explicit execution theorems, automatic formation where
  admitted, and certification; then expansion followed by reverification
  and the audit/profile agreement checks, through the shared engine.
- Update `docs/concepts/resources.md`, `docs/concepts/contracts.md`, and
  `docs/internals/architecture.md` to describe the shared interface, the
  single transition record, and the retained family distinctions. Do not
  document excluded extensions.
- Reconcile [rbtree-example.md](rbtree-example.md) C6 and
  [global-variables.md](global-variables.md) with the final callback
  packaging behavior, then delete this issue and its index line.

## Regression matrix

Positive and paired negative cases. Rows marked "in corpus" name the
fixtures believed to pin the behavior today; W7' confirms the full matrix
rather than trusting this table.

| ID | Behavior | In corpus | Still to add |
| --- | --- | --- | --- |
| R1 | `owns pair(node)` supplies the link for a separate `owns node->right->augmented`; missing authority or guard fails locally. | `contract_owns_composite_argument*.md`, `contract_owns_through_composite_field*.md`, `contract_dynamic_loadable_*`, `contract_nested_*` | none known |
| R2 | The same dependent clause through named callback, execution theorem, automatic formation, and certification. | direct and named paths in the R1 fixtures; `named_contract_rejects_unheld_link_read.md` | execution-theorem and certification variants (W7') |
| R3 | One scoped open, three owned-footprint callbacks, permitted mutation, changed cell and consumed support rejected, no call after the close. | `rb_augment_callbacks_helper_{owns,owns_cell_separate,owns_rejects_unseparated,mutates_body,mutates_body_stepwise,rejects_changed_cell,consumes_suite,rejects_call_after_close,calls_after_close_through_view}.md` | none known |
| R4 | Raw and one-layer `Buffer` have the same checked effects; unrelated cell and token framed; out-of-authority write and view-to-own fail. | `c_contract_executes_buffer.md`, `c_named_function_contract_frames_*`, `c_named_function_contract_rejects_ownership_from_view.md` | none known |
| R5 | Entry-selected `owns` range after a field change; returned instance with identity and fresh fields; no retargeting, invented preservation, or aliased identities. | `field_derived_view_does_not_retarget_after_a_pointer_write`, `c_contract_executes_counter_{forward,wrong_instance,unpromised_field}.md`, `c_call_binder_transport*.md`, `direct_call_map_is_checked_in_kernel_like_named_proof_arguments` | none known |
| R6 | Callback borrows a token or view without a persistent caller view; double consumption fails; scoped views do not escape. | `c_named_function_contract_borrows_*`, `c_named_function_contract_rejects_consumed_*`, `resource_scope_*.md`, `borrowing_composite_survives_an_owning_call.md` | none known |

## Gates and handoffs

Every implementation chunk runs its focused tests and an unfiltered
`scripts/check.sh` in its task worktree before integration; the verdict is
the unpiped exit status, per [testing.md](../docs/internals/testing.md) and
[verification-efficiency.md](../docs/internals/verification-efficiency.md).
A changed hot representation needs deterministic curves over at least four
sizes in the same chunk. Each handoff states the chunk, base and result
commits, files and interfaces changed, tests added with R IDs, exact gate
commands and exit statuses with scaling counters, removed paths or the
adapter's removal owner, remaining blockers classified as verified or
hypothesis, and confirmation that no language semantics, C source, budgets,
quarantine, or unrelated files changed. After any interrupted verifier,
confirm its process tree exited. Do not create new issues for discoveries
without explicit user authorization.

## Acceptance criteria

- Existing syntax and the language-preservation contract are intact.
- R1 to R6 are checked by bounded positive and negative regressions across
  the forms in the matrix.
- One normalized resource specification and one contract interface serve
  direct functions and callbacks, with distinct checked evidence where
  needed, and one transition record is the account of every application
  (D2 settled and implemented).
- Clause evaluation does not lose available authority because an address
  depends on memory inside a folded resource.
- The transition projection is the sole memory-effect source; no surface
  reconstruction can disagree with it (done: no surface footprint exists).
- No memory-DAG or frame query scans compositions unrelated to its subject
  (D1 settled and implemented), with curves pinning the bound.
- Observations survive exactly when their support permits; scoped views do
  not escape except as held escaping borrows; callback facts stay tied to
  the exact pointer value.
- Binder forms share one identity map while preserving return snapshots,
  exclusive identity, and fresh fields.
- `scripts/check.sh` passes on the final integrated commit, the concept and
  internals docs are current, and the rbtree and globals issues reflect the
  landed behavior.
