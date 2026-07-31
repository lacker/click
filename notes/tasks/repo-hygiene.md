# Repo hygiene (needs owner sign-off before deletions)

Status: done (owner approved 2026-07-30; executed same day)
Claimed:

Scope: stale state to clean once the owner confirms:
- Merged branches: claude/engineering-debt, claude/store-provenance.
- Older branches: claude/code-review-design-issues-763cd1,
  codex/click-expand, wip/tactic-certificates-2026-07-18,
  worktree-claude, plus session branches from 2026-07-30 already
  merged to master.
- Worktrees under .claude/worktrees/.
- Stash `store-provenance WIP` (byte-identical to the merged branch's
  first commit — verify then drop).
- Stale /private/tmp worktrees: click-head-audit, click-head-probe,
  click-p0-baseline.

Done when: the owner approves a specific deletion list and it is
executed, or items are explicitly kept with a reason.


## Executed 2026-07-30 (owner approved the full list)

Deleted: 14 merged branches (engineering-debt, proof-panics,
store-provenance, codex/click-expand, code-review-design-issues-763cd1,
9 completed worktree-agent-*), the unmerged
wip/tactic-certificates-2026-07-18 (superseded by the gateway
migration), the store-provenance WIP stash (verified byte-identical to
merged 5e40883 first), 15 stale worktrees (agent worktrees, /tmp
click-head-audit/probe/p0-baseline, previous-session bisect trees), and
~90 /tmp debris files (profiler samples, scratch .click files).

Kept, deliberately:
- claude/forall-extension-wip — prior work for the named-memory-states
  arc, now green-lit.
- worktree-claude branch — ARCHAEOLOGY DONE 2026-07-30, see below. All
  three soundness fixes are on master; the branch is safe to delete
  (owner's call, not done here).
- The two live agent worktrees/branches and the active session branch.


## worktree-claude archaeology (2026-07-30) — verdict: fully re-landed

The branch's single unmerged commit 156f701 "Fix three megakernel
soundness holes (havoc, overflow, fold split)" is a *pre-rebase copy*
of cd90c80, which is on master. Same title, same author date
(2026-06-22 08:03:49 -0400), different parent (156f701 on 35a23a6,
cd90c80 on 1581870). Restricted to src/megakernel.rs the two patches
are textually identical apart from hunk offsets, blob hashes, and one
adaptation to the concurrent uint8 work
(`state.locals.set(name, value)` -> `set_typed(name, value, c_type)`).
cd90c80 was later carried through the kernel split 2561585
(src/megakernel.rs -> src/kernel/*).

Per-fix verdict — all three RE-LANDED, none missing, no repro needed:

| # | Hole | Fix on master | Regression test | Ran |
|---|------|---------------|-----------------|-----|
| 1 | Loop memory havoc left stale cells readable across a loop; address-escaped locals not havoced | `CMemory::with_loop_memory_havoc` cell-drop at src/kernel/primitives.rs:2568-2585; `havoc_loop_modified_locals` escaped-local extension at src/kernel/loops.rs:1328-1370; `address_escaped_scalar_locals` at src/kernel/loops.rs:1433-1453 | mdtests/loop_rejects_stale_pre_loop_store.md, mdtests/loop_rejects_stale_address_escaped_local.md (both survive, updated only for surface syntax: `loop 0` -> `for loop(0)`, `valid_range` -> `loadable` + `consumes`; both still `expect fail: *.stale`) | PASS |
| 2 | Order helpers carried bounds across `base +/- c` using true-integer math, ignoring signed overflow | `subtract_same_const_order_fact` guard at src/kernel/assumptions.rs:2701-2715; `has_add_const_lower_bound_above` at :2815-2825; `has_add_const_lower_bound_at_or_above` at :2859-2868 — all three gate on `signed_{add,subtract}_overflows == Some(false)` | src/kernel/tests.rs:3405 `interval_arithmetic_uses_lower_bound_for_incremented_values` | PASS |
| 3 | Count-fold range split proved `fold(lo,hi) == fold(lo,mid) + fold(mid,hi)` without `lo <= mid <= hi` | `count_fold_split_parts_match` non-reversed sub-range checks at src/kernel/reasoning.rs:1500-1512 | src/kernel/tests.rs:5383 `count_shaped_range_fold_split_is_proven_equal` | PASS |

The guards are demonstrably live, not vestigial: each regression
carries an explicit *negative* assertion (`assert!(!...proves(...))`
for the two unit tests, `expect fail:` for the two mdtests) that only
holds while the guard is in place. Related standing guard:
`memory_load_equality_does_not_ignore_loop_havoc_identity` (also
passes) — see the SOUNDNESS TRAP note in notes/conventions.md.

Gates at verdict time (all green, notes-only change):
`cargo nextest run --lib --bins` 497 passed / 6 skipped;
`cargo test --test mdtests` ok; `cargo test --test examples` ok.

Recommendation: worktree-claude carries nothing master lacks and is
safe to delete. Not deleted here — branch deletion needs the owner.
