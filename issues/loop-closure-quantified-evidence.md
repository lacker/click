# Retain explicit quantified evidence for loop closure

## Violated invariant

Loop preservation still depends on general proof discovery during preparation
in `loops.rs::verify_lowered_invariant_path`. The proof object now retains and
separately validates its results, but the surface planner does not yet replace
all that discovery with explicit proof operations.
An invariant's checked value relation is not, by itself, evidence for every
loadability obligation produced when lowering that invariant.

This is a prerequisite for the loop-closure migration in
[simplify-kernel.md](simplify-kernel.md), not a new load-equality fallback or
permission to change C. The existing fixture is green with legacy preparation;
the missing capability is an independently checkable surface proof for what
that closer currently derives.

## Investigation (2026-09-07, base `0ba70d03`)

A task-worktree prototype removed the general invariant checker, changed the
legacy preflight to `c_loop_invariant_obligations_at_back_edge`, and required
the returned obligations to occur in the proof object's own facts. It also
separated the `close_invariants` request from the checked closure flag. The
basic `count_to_n_loop_invariant.md` fixture and a unit regression rejecting
an unrecorded but derivable scalar invariant passed.

The full gate then failed these three existing expansion tests:

- `bound_universal_outcome_retains_instantiation_and_transport`
- `bound_universal_bubble_pass3_max_suffix_has_no_outcome_fallbacks`
- `bound_universal_bubble_sort3_two_pass_sorted_has_no_outcome_fallbacks`

The first two use `mdtests/bubble_pass3_max_suffix.md`. Its fixed C loop
conditionally swaps `p[j]` and `p[j + 1]`, increments `j`, and preserves
`all_le_range(p, 0, j, p[j])`. The predicate expands to:

```click
forall (k: int32) {
    0 <= k and 0 <= k and k < j implies p[k] <= p[j]
}
```

The exact collector first exposes a separate obligation of the form
`forall k. guards(k, j) implies loadable(p[k..k+1])`, at the current memory
snapshot. A surface `have` for the value invariant does not publish this
separate obligation. The collected goal can also be wrapped in implications
for earlier invariants and lowering prerequisites.

A second bounded experiment synthesized surface `have` goals for the explicit
obligations and tried the existing checked simp planner. It could prove and
publish the quantified loadability fact. Two further distinctions appeared:

1. The surface goal uses a fresh quantified binder (observed ids 2,000,000 vs
   the invariant lowerer's 3,000,000). `proves_exact` does not identify those
   facts. The existing `quantified_equivalence_index_key` also excludes
   `CMemoryLoadable`, so simply using its binder-only comparison does not help.
   A prototype extension indexing loadability by memory arena identity, pointer,
   and byte count allowed this obligation to match without simp. That extension
   has not been validated for scaling, snapshot changes, or arena lifetime and
   is not ready to land independently.
2. With loadability matched, the remaining invariant obligation still failed.
   The existing surface planner returned a prompt miss on both the synthesized
   implication goal and the named invariant. The legacy general kernel prover
   had previously discharged it. This is a surface proof-planning/simple-step
   coverage gap, not evidence of a false C claim. No timeout was observed.

No prototype verifier changes or fixture edits were integrated. The initial
full-gate failure and the subsequent focused failures are not green results.

## Checked-lowering retention (2026-09-07)

The chosen representation is a typed, kernel-owned checked-lowering record.
The legacy planner now retains the exact lowered path, its obligation targets,
their derivations, the goal derivation, and the persistent
path context. Record validation checks supplied derivations and their exact
conclusions; it does not invoke a derivation builder. Keeping the actual
lowered binders avoids a second lowering and alpha-equivalence lookup.

The proof-object adapter constructs these records from its own branch facts
and checked execution facts, and retains them with a shared execution snapshot
and the selected invariant checks. This is archival evidence, not a portable
success token or permission to close a different snapshot. It does not clone
the C state or entire ambient fact history to attach a record.

This is the retention foundation, **not the completed discovery migration**.
The legacy general/simp planner still constructs these proofs. The closure
consumer described below now validates the records separately.

### Complete bundle coverage

Every invariant now goes through retained lowering, including invariants
already established by explicit `have` steps. Removing the old bypass alone
exposed another discarded result: an unfolded predicate `have` proved its
structural body but published only the opaque predicate name. At a loop
frontier, joining that completed scope now retains both the named predicate
and its actually proved unfolded body, with surface mappings for expansion.
Incomplete scopes publish neither; other scope interfaces are unchanged.
No new binder-equivalence rule or global search heuristic was needed.

Records also prove provisional lowering obligations, not just obligations
already marked non-assumable. Their proof context excludes those obligations:
a read-safety requirement cannot serve as its own premise. A known value fact
with missing read safety is rejected. Existing checked execution/resource
facts supply safety without additional user bookkeeping.

The original and expanded bubble-pass fixtures cover this path. Focused tests
also check complete mixed explicit/legacy bundles, missing provisional safety,
incomplete scope rejection, independent explicit `have` checking, and four-size scaling of
the retained-body scope join. This completes coverage, not the removal of
legacy derivation building at closure.

Regressions cover missing/replaced safety evidence, changed goal/context, and
multi-size ambient-fact scaling of record rechecking. The existing bubble-pass
expansion regressions remain the integration requirement.

## Remaining implementation sequence

### Explicit preparation and the binder boundary (2026-09-07)

An experiment removed the legacy prefix probe and its public wrapper, making
region `simp` attempt checked `have` proofs for every named invariant.
The bubble-pass and two-pass original/expanded tests passed, but the full
fixture gate failed on `copy3_array_demo.md` and `loop_entry_snapshot.md`.
The former lost the proof of invariant 2 after the additional facts; the latter
failed to lower a `have` because the loop-entry label `drain` was unavailable
in that ordinary scope. The probe removal was therefore reverted too. The
existing runtime remains unchanged; only the defensive binder regression and
this investigation are retained.

An experiment also emitted `have` proofs for separately collected read-safety
obligations. Those proofs verified, including after expansion, but introduced
substantial extra search in the two-pass fixture. Filtering out value goals
whose premises merely mention read safety reduced that cost, but did not
eliminate it. That planner addition was removed rather than accepting the
slowdown. Finishing should not rely on repeated generic `have` search for
every collected obligation.

In the bubble-pass census, the remaining legacy value tree was a universal
introduction, implication introduction, and typed universal instantiation.
The read-safety tree ended in a legacy atomic leaf. With the experimental
surface safety proofs, both goals had binder-equivalent facts in the context, but not facts
with the invariant lowerer's exact bound-variable identities.

A prototype replaced preparation's derivation builders with exact fact
consumption plus a snapshot-sensitive binder key. The bubble-pass original
and expanded proofs passed. A new adversarial test then rejected that design:
bound variables can occur inside the saved snapshot itself. Let memory `M(i)`
have a cell whose stored value is variable `i`. These are not equivalent:

```text
forall i. load(M(i), cell) <= i
forall j. load(M(i), cell) <= j
```

The first binds the occurrence inside memory; the second leaves it free.
A key containing the same memory identity and an ordinal for the outer binder
incorrectly equates them. The existing full substitution comparison correctly
distinguishes them. Its negative regression is retained in
`quantified_binder_comparison_respects_occurrences_inside_snapshots`.
The unsafe key/index and exact-only preparation prototype were removed; no
new binder comparison or derivation-builder replacement landed from it.

The selected interface is to expose the actual lowered value/safety goals as
proof-object scopes, so their proofs already use the retained binder identities.
Adding a proof body to `close_invariants` was approved on 2026-09-08; see the
prototype findings below. The alternative is a typed renaming proof with
explicitly checked snapshot freshness/dependency evidence. Do not use the old
snapshot-blind key as authority, or add a whole-memory traversal per simple
step to repair the failed key. Any new renaming rule must reject the example
above and include deterministic scaling with growing unrelated snapshots.

### Closure proof-body prototype (2026-09-08)

A task-worktree prototype added `close_invariants by { ... }`, retaining the
existing `close_invariants();` form. It collected the exact lowered value and
read-safety goals into one conjunction and checked the body against that
kernel goal. Provisional safety obligations remained separate goals, not
premises of their own proofs. The completed proof was bound to its exact root
premise store, current execution snapshot, and checked execution facts.

A scalar counting-loop regression passed ordinary verification, whole-claim
expansion, and verification of the expanded source. An empty closure body was
rejected instead of falling back to legacy discovery. These are focused
prototype results, not a completed migration or a full-gate result.

The unchanged C from `bubble_pass3_max_suffix.md` exposed a further interface
gap. Its ordinary expanded proof verified; replacing its bare closers with
`close_invariants by { simp(); }` promptly failed. The exact combined goal did
have a synthesized surface presentation. However, the structural conjunction
arm of `try_structural_simp_closure_with_surfaces` proves each conjunct through
an ordinary `begin_have(surface)` before applying `split()`. Those nested
`have` scopes lower the surface proposition again. Opening only the outer
exact goal therefore does not preserve exact goal identities throughout its
subproofs. This identifies a remaining architectural gap; it does not establish
that fixing this one arm alone will complete quantified planning.

The chosen exact child-goal construct is now `both { ... } and { ... }`.
It opens the exact kernel conjuncts in isolated sibling scopes and retains
their proof bodies through expansion. Structural conjunction planning now uses
these scopes too, including after rewrites and within proof branches. The
current `split()` remains unchanged: it checks a conjunction from
already-established facts. The remaining work is to connect the approved
`close_invariants by { ... }` body to exact lowered obligations. The `by`
distinguishes a proof of closure obligations from an execution region. This
syntax is selected but is not yet implemented. Do not silently make
`have` select a kernel goal by a same-written surface formula: that revives
the snapshot/binder ambiguity this interface is intended to remove.

All runtime and syntax changes from this prototype were reverted. The
scalar prototype's success is not evidence that the new syntax is available.
The acceptance tests must include original and expanded quantified proofs,
incomplete bodies, substituted child proofs, changed premises/snapshots, and
four-size deterministic scaling of scope entry and completion.

### Prepared-bundle consumption (2026-09-07)

The loop planner now calls `prepare_loop_invariant_bundle` before closure.
`certify_loop_invariant_bundle` consumes that result through the kernel proof
object's `validate_checked_invariant_lowerings`; neither consumer lowers the
invariant again nor invokes a derivation builder. Missing evidence fails even
for a derivable scalar goal and even after a source `close_invariants` request.
The old flag and its setter are named as requests, not checked closure.

The opaque complete bundle binds the selected invariant checks, shared C-state
snapshot, exact premise-store root, and checked execution-fact storage. Closure
rejects replaced snapshots (even structurally equal ones), changed premises,
changed checks, incomplete path coverage, and invalid supplied path proofs.
The binding checks are constant-time storage comparisons; proof checking is
charged to the supplied evidence. A four-size deterministic regression covers
the whole kernel consumer against growing unrelated fact stores.

This separates construction from consumption; it does **not** remove the
general/simp construction ladder from preparation. The prefix probe was
retained after the failed explicit-preparation experiment described above.
Expanded source still prepares internal lowering records while being checked.
Removing that discovery, and replacing the independent state-join reasoning,
remain separate migration work. Do-while paths proven unable to continue need
no back-edge bundle and retain the existing exit classification.

### Still outstanding

1. Keep `bubble_pass3_max_suffix.md` and its C unchanged. Connect the newly
   explicit value/safety proofs to the exact lowered goals without
   an unsafe binder shortcut. Prefer exact lowered-goal scopes; if using
   renaming evidence instead, implement the snapshot-dependency regression
   and scaling requirements above before consuming it as authority.
2. Replace the planner's internal general/simp derivation construction with
   explicit proof operations while preserving complete path and safety coverage.
   Retain actual proofs without trusting surface spellings or requiring
   redundant read-safety bookkeeping from users. Exact retained lowering
   consumption does not require alpha-equivalence indexing.
3. Remove `verify_lowered_invariant_path` and its general/simp derivation ladder
   only after the original and expanded fixtures pass through the replacement.

## Acceptance criteria

- The original bubble-pass and two-pass sorting fixtures verify, and their
  expanded simple scripts recheck without kernel invariant proof discovery.
- A multi-path invariant requires evidence for every live path and every
  non-assumable lowering obligation. Removing one proof, substituting another
  path's proof, or changing its snapshot is rejected.
- A merely derivable but unrecorded scalar invariant is rejected by exact
  closure; an explicitly proved invariant succeeds.
- Simple closure work is bounded by named invariants/evidence and logarithmic
  indexing, not unrelated fact or execution history size.
- `scripts/check.sh` passes, and the issue is deleted when implementation,
  regressions, and documentation land.
