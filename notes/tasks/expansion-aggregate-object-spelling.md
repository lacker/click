# Expansion loses the aggregate `object(owner)` spelling

Status: done (2026-07-31, branch worktree-agent-a5226ef393a7511d7)
Claimed:

The last remaining lib `#[ignore]`:
`expansion_preserves_unfolded_resource_and_predicate_fact_spellings`
(src/lang/click/expansion.rs) now passes un-ignored.

## Root cause

`unfold` does not itself decompose the declared aggregate — the body
fact `separate(memory(object(owner)), memory((owner->data)[0..owner->cap]))`
lowers to a single kernel `CResourceSeparate` and gets its spelling
recorded (proof.rs `unfold_composite_resource`). The loss happened at
premise emission (`record_surface_replay_tactic`, CertifiedStatementStep
arm): the ambient context carries the six pairwise per-field
separations, each fails the exact-match reconstructibility check
against the resource projection (which merges adjacent owned ranges),
so each piece is spelled individually — the pieces even have their own
recorded pairwise spellings from
`record_observed_composite_surface_facts`. The aggregate itself IS
exactly reproduced by the merged projection, so it was skipped as
reconstructible. Net effect: decomposition spelled, aggregate never.

## Fix (premise-emission layer, proof.rs)

A `CResourceSeparate` premise carried only as an ambient permission
(not selected by a derivation) re-folds into a strictly stronger
source-spelled available separation that entails it — the declared
aggregate — before surfacing. Guards:

- base-pointer prefilter: only memory-range candidates whose
  (left, right) bases match the fact's, in either orientation, get an
  entailment check (without this, the kernel derivations ran during
  smart-tactic certificate recording and pushed
  `composite_resource_clone_separate_target.md`'s execute_rest from
  ~0.4 s to 4.7 s, over the 2 s smart budget);
- arithmetically true separations (same base, disjoint constant
  ranges) are derivable from any premise set, so entailment cannot
  pick a fold target — they keep their own (pairwise) spelling;
- strictness: the candidate must not be entailed back by the fact;
- entailment assumptions are built lazily, once per candidate.

Emitted block for the test now reads: three intra-object pairwise
separations (canonical per-field spellings, from the owns clauses) plus
one `fact separate(memory(object(owner)), memory((owner->data)[0..owner->cap]));`
replacing the three field-vs-slice pieces.

## Test tightened

The old `terminated_at` assert only matched the resource declaration
echoed in the expansion. The asserts are now scoped to the emitted
`step using` block: aggregate spelling present, per-field decomposition
of the aggregate absent, unfolded predicate body
`owner->data[owner->len] == 0` present, `terminated_at` absent from the
block (the proof unfolds it) but preserved in the declaration echo.
The test also re-verifies the expanded certificate
(`verify_c0_sources`), so the folded premise is known to replay.

## Gates

`cargo nextest run --lib --bins` 530/530, `cargo test --test mdtests`
green (including the budget-sensitive
`composite_resource_clone_separate_target.md`, 0.45 s serial),
`cargo test --test examples` green.

Overlap note for siblings working proof.rs: the change is confined to
the premise assembly inside `record_surface_replay_tactic`'s
`CertifiedStatementStep` arm (spelled-separation candidate list + fold
before `checked_surface_comparison_fact_at_point`); certificate
recording and per-path merge were not touched.
