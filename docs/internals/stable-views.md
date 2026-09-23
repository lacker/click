# Stable views

This page is the durable design record for the meaning of `views` in the
kernel: a shared borrow whose covered memory stays unchanged and allocated
while the borrow is active. It records the laws, the representation, the
transitions, the call boundary, the limits, and where each rule is pinned by
a test. The public meaning for contract authors is in
[Resources](../concepts/resources.md); the kernel layout is in
[Kernel implementation](kernel.md) and [Separation logic](separation-logic.md).
The campaign that landed it, "fix-views", ran from 2026-09-11 to
2026-09-14; its dated checkpoints are in the git history of
`issues/fix-views.md`.

## Meaning

`owns memory(R)` is exclusive usable authority over the selected range; a
direct read needs no separate view. `views memory(R)` is shared, read-only
authority for a borrow scope: the covered contents and the allocation
lifetime stay stable until the scope ends. Two views of overlapping memory
may coexist; readers never prove disjointness. Usable ownership and an
active independent view of overlapping memory cannot coexist: the lender
keeps a recovery entitlement, not usable write authority. Ownership and a
view of disjoint ranges coexist, and writes to the owned part preserve the
viewed part. A view of a structural resource preserves its selected
structure, its memory dependencies, and its advertised facts for the scope.

Even a same-value store conflicts with a view: stability excludes
conflicting access rather than checking equality afterwards. Initialization
writes, bytewise stores, deallocation, lifetime end, and opaque call effects
obey the same rule. A view freezes the range selected at borrow entry and
never retargets when a pointer-valued field changes; a view of a pointer
cell does not protect the pointee unless the resource body includes it. An
empty range grants no dereference, protects nothing, and proves neither
nonnullness nor a live allocation.

## Laws

Every transition below preserves these laws with an arbitrary compatible
frame present.

1. Authority conservation: a byte range's write authority is usable in one
   component, suspended in a loan, or transferred. Suspending it leaves no
   usable copy in a folded owner, an implicit stack capability, a callback
   frame, or a remembered composition.
2. Reader stability: while a view has valid access authority, no compatible
   component can write or invalidate its bytes.
3. No view-to-owner entailment: recovering ownership is a transition with
   closure evidence and the unique recovery entitlement, never an
   entailment, a normalization, a fold, or a theorem.
4. Descriptor/authority separation: copying, dropping, or deduplicating a
   description changes no live share and no recovery entitlement.
5. Exact identity: scope, loan, allocation lifetime, resource occurrence, and
   support generation are semantic identities; equal spellings and equal
   values do not identify them.
6. Supported facts retain support: an owner-supported observation is usable
   only through its current support; a loan-supported one also needs the
   active loan; a fact about an old snapshot is history, not authority.
7. Locality: rule checking touches the named authority and its indexed
   dependencies, never the whole frame.
8. No authority from unknown aliasing: a lending partition needs checked
   separation or shared backing; failure to prove overlap is not
   disjointness, and two read requirements may alias.
9. Branch conservation: alternative paths each reason from the entry
   resources; a join never adds their capabilities together.
10. Checked orchestration: tactics, lowering, and search propose
    transitions; the kernel checks each against the actual predecessor and
    its evidence.

## State

The loan ledger (`src/kernel/loans.rs`) lives in the checked state root
beside the resource context and is shared by ordinary evaluation, modular
calls, proof execution, and certification. It is persistent, indexed, and
opaque: every transition produces evidence bound to the exact predecessor
state identity, and identity changes only on authority-changing transitions.

| Record | Holds |
| --- | --- |
| Scope | Fresh identity, active flag, root share, close entitlement, parent scope and pinned parent share, dependent child scopes, holds. |
| Loan | Scope, supporting occurrence, escrow (the suspended owned pieces), permitted descriptions, origin (escrowed, reborrowed, or borrowed contract input), memory backing. |
| Share | A node of a binary split/join tree for one scope: holder, parent, children, pinning child scope. |
| Binding | Per resource occurrence in the resource context: loan, scope, share, support, the viewed description, and an optional hold. |
| Indexes | Concrete active memory intervals (dyadic), symbolic protected ranges per block, and the count of loans that protect memory. |

Descriptions are copyable; shares are conserved; the close entitlement is
unique; recovery happens once per escrow. Only the reconstructed root share
can end a scope. A binding is what carries authority into a resource
occurrence; the resource context's dependency root is the canonical copy
and the state mirrors it.

## Transitions

| Operation | Evidence | Result |
| --- | --- | --- |
| Lend | Usable ownership, a fresh scope | Escrowed owner, recovery entitlement, a description and the root share for the borrower |
| Lend composite | An owned head with its checked one-level frontier | The head escrowed, primitive pieces indexed for protection, nested composite and viewed pieces admitted as descriptions without byte backing |
| Borrowed contract input | A contract `views` clause at function entry | A root with no close right: the lender lives outside the modular proof |
| Reborrow | A live parent binding | A child scope pinning the parent share; the child carries only the description that authorized it and the backing under it |
| Split, join, transfer | Exact siblings and holders | Conserved shares |
| Project | The kernel's one-level expansion of a permitted composite view | A derived description on the same loan, identity unchanged |
| Hold, release | A live binding | A restriction on the scope that End refuses while it exists; each change mints a fresh ledger identity |
| End | Close entitlement, full root share, no dependents, no holds | The scope ended, the parent share unpinned |
| Recover | An ended scope and the unique entitlement | The escrow restored exactly once |

Projections keep the ledger identity because each description is
re-derivable from its parent by a checked expansion. Holds and releases mint
fresh identities because they change whether a scope may end, which joins and
evidence checks must distinguish. The composite's binding also carries the
hold, and every join and recovery compares bindings.

## The call boundary

Calls are planned jointly and body-independently. Exclusive (`owns` and
`consumes`) requirements are reserved first, from a direct owned entry, from
a held owned composite opened one level, or definitionally when the
requirement's expansion is empty. Views are then backed: from an owner by
lending the requested subrange and keeping the remainder usable, from the
caller's own view by a reborrow, from an owned composite by a composite
lend, and from a different owned composite or the caller's owned frontier
when the viewed composite's checked expansion is covered piecewise and its
facts hold at the call. A view of live caller-local storage with no explicit
resource is backed by a checked local-storage loan. Its byte range must fit
inside the live allocation. Checked entry storage includes fresh by-value
aggregate parameter copies as well as the caller's original locals. The loan
grants a callee share and a caller close
right, but escrows no owned fact; closing it restores implicit access without
adding an ownership resource. Read-only storage retains intrinsic read authority
and is neither lent nor recovered. Cross-clause conflicts (an owned clause
overlapping a viewed one, or an owned piece inside a viewed frontier) are
refused at planning as proven overlaps.

A declared mutable effect is a consequence of the transferred authority.
Each effect range is compared with the full checked view frontier; an effect
and a view reserved from distinct caller occurrences are disjoint by the
partition invariant, while the same occurrence needs an arithmetic proof.
Every path that retires an allocation, definite or of undecided continuity,
consults the ledger that carries the call's own loans. Automatic lifetime ends
also consult it: normal scope exit, return, break, continue, jump, exception,
and the retained proof event refuse to retire a block with a live loan.
The same ledger already guards direct local assignments and alias stores,
including same-value writes. A nested reader reborrows the local loan through
its exact resource binding. No new surface clause is needed.

For a suspended modeled-pthread worker borrowing a parent view, the checked
entry splits the parent's current share. The parent retains one sibling and
the worker reborrows the other. A join ends that worker's child scope, returns
its share, and joins only available siblings on that share's ancestry path.
The parent binding advances when its retained share is recombined, so any
other live child stays pinned and the original root returns only after every
share is back. For implicit local storage, the first worker opens one checked
local root held by the parent. Later workers split its retained share rather
than opening another root. The thread ledger indexes the parent's local share
by the exact viewed fact, without adding a resource fact to the parent. Each
join returns its own share; the final join closes the root and restores
implicit access. The thread ledger also retains the checked sequence's origin
and current loan roots across function return for contract certification.
For an explicitly owned memory piece, the first worker escrows that piece in
a parent-held root. Its checked view remains in the parent resource context;
later workers split that view's retained share. The final join removes that
exact bound view occurrence before recovering the owner. Ordinary resource
consumption cannot remove a view description, so this removal requires the
loan binding and occurrence identity checked at recovery.

At return, obligations are validated before recovery: the callee's shares
are transferred back, call-created scopes end, escrows are recovered, and the
evidence (entry transitions, releases, recovery transitions, the recovered
ledger) is rechecked from the callee root. A returned view is accepted only
as a lent input, through a preserved outer binding, as a projection of a
returned owner, or as read-only storage. Every produced composite's one-level
frontier is checked against what the caller holds across the call, escrowed
owners included, so a produced body cannot duplicate authority.

### Escaping borrows

A composite whose body packages a loan-backed view is a struct holding a
borrow. Folding it places a hold on the loan's scope, carried by the head's
binding; unfolding hands the binding to the restored piece so a refold reuses
the hold. At a call boundary, every viewed piece a produced or returned owned
composite packages must be backed by exactly one loan of the call: a view
lent here (the loan is returned open with the composite holding it: an
escrowed owner stays escrowed, a child of the caller's view ends and the
parent binding is held), or the hold binding an owned input brought in. None
or more than one is refused. A consumed composite releases its hold, and a
root the caller can then close is ended and its owner recovered inside the
recovery. This is Rust's lifetime elision: nothing is written in the
ordinary case, and the ambiguous case is a diagnostic.

## Footprints and storage

Footprints are bytes. Coverage, subtraction, overlap, and entailment of
memory resources are decided bytewise across element widths; a load's width
is about its value. Overlap with symbolic bounds is refused only when
proven: the partition invariant makes owners in a valid context disjoint
from views by contract meaning, so an unproved separation between an owner
and a symbolic view is not a conflict, while a declared effect against a
view fails closed. Concrete active loans live in a dyadic interval index;
symbolic protected ranges live in a per-block bucket, and a symbolic query
beside concrete loans is refused as unsupported.

A nonempty subrange loan prevents freeing or reallocating its allocation.
Locals, heap, and globals use the same access checks; a `static const`
block is read-only storage with permanent read support and is not a way to
give mutable memory an unbounded loan. Loop-head and interface havocs keep a
cell only when a loan protects it and drop zero-width cells.

## Facts, observations, and composites

An owner may read directly and observe its composite without lending to
itself: the observation is a projection recorded against the owner's
occurrence and disappears with it. A borrowed composite's observations keep
the loan identity through projection, fold, unfold, `open`, `close`,
normalization, range splitting, and callback-fact extraction. Three outcomes
stay distinct: a copied value or a snapshot proposition may remain true
after a loan ends; a claim about the current cell needs checked framing;
permission to load needs current authority.

A composite body's facts may be covered by a stable view when they depend
only on memory the loan stabilizes; a fact that counts a population or
claims allocation liveness is not loan-stable and such a composite cannot be
lent. A fold whose body has facts cannot view memory the folding context
itself owns: that view is only an observation, the owner could still write
the bytes, and the folded facts would outlive the values they describe
(`mdtests/fold_cannot_view_memory_its_context_owns.md`). A body without
facts of its own may observe its context's owner. A valid context is a partition: distinct owned occurrences are
bytewise disjoint, composites included, and the kernel does not reason
inside a folded composite beyond its one-level frontier. The frame check
that keeps a loaded cell's name across a call or loop havoc obeys the same
boundary: it opens each owned composite of a published composition one
level and frames a cell only from an owned range that opening exposes. Counted populations
keep the population-wide reading: a unit's body enters the caller where the
population is activated, and its viewed pieces are observations rather than
escaping loans.

## Loops and branches

An outer view stays active through loops; per-call loans close before the
backedge, and the loop's loan identity, participant, and bindings must match
at the head. A join requires identical ledger identity, participant, and
bindings across arms, so a loan ended on one arm cannot join into
unconditional ownership. Proof rebases require identical loan authority.

## Certificates, diagnostics, and complexity

Loan transitions are part of the proof object; expansion, profile, and
audit run under the same rules and agree with verification. Refusals carry
a category, the operation, a bounded subject, identifiers, and the origin;
proven overlap is distinguished from unproved separation. Artifacts carry a
resource-semantics version so no artifact minted under the retired
interpretation certifies a claim. Version 3 includes checked implicit-local
loans and automatic lifetime retirement.

Shares, loans, and support are indexed by identity; memory by allocation
and range; dependencies by their immediate parent. Persistent edits are
logarithmic. The known violation of the
[efficiency contract](verification-efficiency.md) is the loan-preserving
havoc, whose cost is cells times symbolic loans in one block; it is pinned
as a measurement.

## Suspended worker recovery (internal checkpoint)

`src/kernel/threads.rs` uses the same checked partition and verified-call
summary as synchronous calls, but keeps the worker's output resources and
postconditions in an opaque completion registry. Spawn requires termination
evidence for the exact verified function. Failed creation preserves the
parent; an empty or ambiguous summary refuses rather than removing its path.
Successful creation exposes only the mutable-footprint havoc to the parent.

Join composes the explicit worker output delta into the current parent frame
and closes just that worker's loans against the current ledger. It never
restores the saved parent ledger or memory. This permits two disjoint workers
to join in either order while the other worker's job view stays protected.
A registry entry is consumed once; a foreign handle or a user resource token
cannot authorize recovery. The runtime assumption that a valid join succeeds
is explicit and scoped to this parent's live, terminating child.

This is an internal ownership checkpoint, not a C threading API. It supports
explicit external-memory ownership and nonescaping stable views, including
views backed by live local storage without an ownership annotation. The local
loan remains active from spawn to join, so the parent cannot write its viewed
bytes or end the allocation lifetime early. Exclusive transfers of
caller stack/global/static storage are refused until ordinary accesses to that
storage enforce thread authority; dropping an ownership fact alone would not
block the caller's implicit storage access. A reborrow pins its
parent share, so a second overlapping reader is refused until explicit share
splitting and recombination are implemented at the thread boundary. Pthread
imports, handle stores, result branches, artifact integration, heap protocols,
and composite or escaping borrows remain outside this checkpoint.

## Model-only extensions

`src/kernel/tests/loan_model_tests.rs` is an executable model with a
bounded search that checks, beside the production rules, two-context
partition and transfer, shared readers across contexts, shared and exclusive
reborrows, a returned field loan, a mutex handle with an invariant-owned
payload and one guard, and a thread-local cell confined to its context.
These are checks of the abstraction boundaries for later threading and Rust
work, not verified concurrency: scheduling, atomics, Rust's alias rules,
exclusive production reborrows and C thread APIs remain outside this checkpoint.

## Regression map

| Rule | Tests |
| --- | --- |
| Lend, read, close, recover, write; same-value store refused | `checked_two_reader_lifecycle_recovers_exact_escrow_once`, `owner_authorized_write_into_a_lent_range_is_refused`, `owner_authorized_same_value_store_into_a_lent_range_is_refused`, `owner_authorized_aggregate_copy_into_a_lent_range_is_refused` |
| Shares and scopes | `splitting_and_joining_require_exact_linear_siblings`, `shared_reader_recovery_rejects_wrong_sibling_reuse_and_stale_branch`, `nested_reborrow_must_rejoin_each_parent_before_scope_end`, `an_old_descriptor_is_refused_after_a_fresh_scope_over_the_same_resource`, `checked_call_evidence_rejects_stale_or_swapped_recovery` |
| Aliased views and nested readers | `candidate_joint_planner_reuses_one_escrow_for_two_aliases`, `candidate_rejects_new_output_view`, `mdtests/stable_view_nested_reader.md` |
| Partial borrows and widths | `mdtests/stable_view_partial_borrow.md`, `bytewise_overlap_is_decided_across_mismatched_element_widths`, `memory_entailment_relates_two_spellings_of_one_byte_footprint` |
| Free and realloc under a loan | `active_stable_loan_rejects_overlapping_heap_free_and_realloc`, `undecided_continuity_retire_refuses_a_lent_allocation` |
| Local loans, bounds, and lifetime | `candidate_local_array_view_uses_a_checked_loan_and_recovers`, `thread_local_view_blocks_writes_and_all_scope_exits_until_join`, `automatic_lifetime_event_rejects_active_local_loan_and_forged_retirement`, `local_views_preserve_aliases_check_bounds_and_mint_no_owned_escrow`, `mdtests/stable_view_local_job.md`, `local_job_views_expand_and_reverify_without_ownership_annotations` |
| Locals and empty views | `active_stable_loan_rejects_direct_local_assignment_and_alias_store`, `candidate_local_array_view_out_of_bounds_is_refused`, `mdtests/empty_view_authorizes_nothing.md` |
| Entry footprint | `field_derived_view_does_not_retarget_after_a_pointer_write` |
| Composites | `composite_loan_protects_primitive_frontier_and_restores_head_once`, `projection_extends_permitted_descriptions_without_a_transition`, `candidate_composite_with_unstable_facts_is_refused`, `candidate_composite_view_is_backed_by_a_covering_owned_composite`, `mdtests/produced_composite_body_overlapping_a_held_owner.md` |
| Frame check at the frontier | `frame_check_opens_owned_composites_one_level_and_charges_per_head`, `mdtests/call_havoc_keeps_names_by_ownership.md` |
| Open and close | `mdtests/rb_augment_callbacks_helper_mutates_body_stepwise.md` (a viewed open closes the same way from a step as from `execute()`), `execution_open_scope_owns_entry_body_and_close_transactionally` |
| Escaping borrows | `a_hold_blocks_ending_the_scope_and_changes_identity`, `escaping_borrow_keeps_the_loan_open_until_the_composite_is_consumed`, `consuming_the_composite_recovers_the_owner`, `mdtests/borrowing_composite_survives_an_owning_call.md`, `examples/input-cursor` |
| Effects | `candidate_rejects_mutable_effect_overlapping_a_composite_view_piece`, `candidate_allows_a_mutable_effect_reserved_from_another_owned_occurrence` |
| Callbacks and refinement | `stable_view_refinement_uses_checked_variance_for_subranges`, `mdtests/rb_augment_callbacks_helper_owns_rejects_unseparated.md`, `mdtests/rb_augment_callbacks_helper_calls_after_close_through_view.md` (a viewed suite's callback stays callable after an open closes), `mdtests/rb_augment_callbacks_helper_rejects_call_after_close.md` (an owned suite's does not) |
| Loops and branches | `loop_havoc_requires_a_checked_set_disjoint_from_active_loans`, `loop_back_edge_refuses_a_dropped_share_or_a_regenerated_root`, `abstract_join_rejects_a_loan_ended_on_only_one_arm` |
| Suspended workers | `src/kernel/tests/thread_transition_tests.rs` (both join orders, linear completion rights, refusal paths, scoped termination, withheld guarantees, backing lifetime, and four-size recovery scaling) |
| Evidence | `hostile_transition_payload_is_rechecked`, `transitions_are_bound_to_their_exact_predecessor`, `session_rejects_a_stale_identity_before_reverification` |
| Scaling | `local_view_work_tracks_the_explicit_delta_not_ambient_local_storage`, the four-size curves in `src/kernel/loans.rs`, `interface_binding_inheritance_is_near_linear_in_the_binding_count`, `loop_head_havoc_work_over_cells_and_symbolic_loans` |
| Model | the `r27_`, `r28_`, `r29_`, and `r30_` tests in `loan_model_tests.rs` |
