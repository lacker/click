# Retain explicit quantified evidence for loop closure

## Violated invariant

Loop preservation still depends on general proof discovery in
`loops.rs::verify_lowered_invariant_path`. Replacing it with exact fact checks
is blocked by evidence that the current surface loop planner does not retain.
An invariant's checked value relation is not, by itself, evidence for every
loadability obligation produced when lowering that invariant.

This is a prerequisite for the loop-closure migration in
[simplify-kernel.md](simplify-kernel.md), not a new load-equality fallback or
permission to change C. The existing fixture is green with the legacy closer;
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

## Intended regression and implementation sequence

1. Keep `bubble_pass3_max_suffix.md` and its C unchanged. Construct an explicit
   surface proof of the updated quantified invariant and its lowering safety
   obligations using the existing statement evidence. Identify any missing
   simple rule before broadening smart search. Do not call the legacy closer
   as a successful preflight that skips generating this proof.
2. Decide how checked lowering evidence is retained: explicit surface facts
   are one option; a typed record binding the checked lowering, path, snapshot,
   and proof is another. The latter must not trust a surface spelling as proof,
   and must have an independently checkable representation after expansion.
   Avoid requiring users to write redundant safety bookkeeping for each read.
3. Support exact alpha-equivalent quantified safety facts, if that is the chosen
   representation, without semantic simp or scans over unrelated snapshots.
   Test renamed binders, changed free variables, different pointer/byte ranges,
   and changed memory snapshots. Include deterministic multi-size scaling tests.
4. Consume the evidence at the kernel proof-object closure boundary. The current
   `close_frontier_invariants` flag update records intent before bundle checking;
   it must not become proof authority on its own. Handle the collector's path
   implications explicitly and reject missing non-assumable obligations.
5. Remove `verify_lowered_invariant_path` and its general/simp derivation ladder
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
