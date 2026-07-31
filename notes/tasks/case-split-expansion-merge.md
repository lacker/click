# Faithful expansion of pure case-split certificates

Status: done (2026-07-31) — fix on branch claude/nervous-ptolemy-90e738,
awaiting coordinator review/merge
Claimed:

Two quarantined mdtests (`sort3_sorted.md`, `bubble_sort3_loop_sorted.md`)
had smart simps over budget (2.2 s / 3.5 s) whose expansion printed an
`if` tree with empty branches that did not re-verify (path 5 of expanded
sort3 could not close `sorted(p, 3)`).

## Diagnosis (final, deeper than the original theory)

The printed tree was never the simp's certificate at all. Probing the
deferred capture (`finish_ordered_proof_replay`, proof.rs) showed:

- Every per-path contribution (`ClosedClaim::claim_tactics`) was EMPTY:
  the simp closed each path's claim by exact check / grouped transition,
  which by design contribute no surface tactics ("their tactics belong to
  the path's tactic list, not to one claim").
- The `if` tree was `DeferredTacticCapture::branch_skeleton` — the
  branch skeleton of the ENCLOSING `execute_rest()`/`bounded_execute()`
  surface replay (built by `synthesize_surface_paths`), grafted around
  the empty leaves purely to make the capture non-empty.

Grafting that skeleton after an unbranched `execute_rest()` is
unfaithful: proof-level `if` conditions at path end lower at EACH
path's own outcome (`introduce_proof_case_assumption` pushes
`fact: None` at exit; the drain lowers per path), and every (leaf ×
path) pair must close — a cross product. Certificate replay only ever
checked the diagonal (each path under its own trace). Concretely, for
path 5 (no swaps, outcome memory = initial memory) the then/then/then
leaf's conditions lower to initial-memory comparisons that literally
contradict path 5's branch facts (same `ConditionIs` term, both
booleans present), the path-end check has no ex falso, and the extra
contradictory facts even poison the derivation that succeeds without
them.

Key confirmations:
- Deleting `simp();` outright from both mdtests verifies: sort3 0.39 s,
  bubble_sort3_loop 1.88 s. The whole smart-simp content was redundant
  scaffolding; the ordinary path-end check closes every path.
- Expanding the `execute_rest()` site (sort3_sorted.md:47:9) emits the
  genuinely paired form — proof-ifs at the branch points with
  `step using {...}` inside the arms — where each leaf carries exactly
  one execution path. The pairing lives there, not at the simp site.
- The existing graft IS faithful when leaves hold self-contained
  derivations (premises include the leaf's own conditions, which are
  available on every path) — that shape is pinned by
  `selected_branched_post_execution_{apply,have}_merges_path_certificates`
  and still verifies. Only empty-leaf grafts are wrong.

## Fix

- `finish_ordered_proof_replay` capture: when every per-path
  contribution is empty, the exact expansion of the selected tactic is
  empty — skip the skeleton graft entirely.
- `finish_tactic_expansion_capture` gains `allow_empty`; only the
  deferred-capture site passes `true` (other callers keep the empty
  guard, where emptiness means lost tactics).
- `expand_c0_tactic_source_at`: an empty replacement removes the
  selected tactic's whole source line when nothing else shares it.

So `click-expand mdtests/sort3_sorted.md:50:9` now deletes `simp();`
(and likewise for bubble). Both mdtests updated that way and
de-quarantined (tests/mdtests.rs).

## Why replay and expansion now agree

Replay's accepted evidence for these claims is "exact check per path,
no claim tactics". The expansion now emits exactly that: nothing. The
re-split tree the old merge printed asserted a case split replay never
performed at that point.

## Dead ends (do not re-attempt)

- `assumption();` as a leaf filler — fails replay because leaves hold
  no open goal.
- Keeping the skeleton with empty leaves — the re-split is semantically
  wrong (cross product, outcome-lowered conditions), not just weakly
  proved; ex-falso in the path-end check would be a new prover arm and
  still unfaithful to the accepted evidence.

## Validation

- New lib test `selected_pure_case_split_simp_expands_by_removal`
  (src/lang/click/tests.rs, next to the graft round-trip tests) pins
  removal on the sort3 shape: expansion contains no `simp()` and no
  re-split `if`, and the expanded source verifies. Note: a 2-cell
  sort2 does NOT reproduce the all-empty shape (its no-swap path gets a
  `have` certificate → graft path, which is fine and still verifies).
- Gates all green: `cargo nextest run --lib --bins` 530/530 (3.4 s),
  `cargo test --test mdtests` 6.3 s including both de-quarantined
  tests, `cargo test --test examples` 6.7 s.

Repro of the fixed flow:
```
cargo run --quiet --bin click-expand -- --time-limit 5m mdtests/sort3_sorted.md:50:9
MDTEST_FILTER=sort3_sorted cargo test --test mdtests
MDTEST_FILTER=bubble_sort3_loop_sorted cargo test --test mdtests
```

Overlap note: `synthesize_surface_proposition` /
`checked_surface_fact_at_outcome` (certificate-spelling-gap task) were
not touched; the changes live in the capture path of
`finish_ordered_proof_replay`, `finish_tactic_expansion_capture`, and
`expansion.rs`.
