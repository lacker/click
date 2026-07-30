# Handoff — 2026-07-29

Written by a departing Claude session for the next Claude working in this
repo. Read this before touching anything. This file and
`language-proposals.md` are intentionally untracked; delete them once their
contents have been absorbed or turned into issues.

## Repo state map

- **master** is at `cce4e3d`. It includes the recent kernel soundness fixes
  (theorem-minting API hardening, struct ABI padding, C comments/unary
  minus/declaration initializers).
- **The main checkout (`/Users/lacker/click`) has uncommitted changes** in
  `src/kernel/*` and `src/lang/click/*` — a previous agent's in-progress
  "certified store provenance" refactor. **Do not discard them blindly**,
  but know that they are byte-identically captured as the first commit of
  branch `claude/store-provenance` (verified by diff hash on 2026-07-29).
  If you need a clean master checkout, verify `git diff | shasum` still
  matches that branch's WIP commit, then it is safe to stash or reset.
- Worktrees / branches of interest:
  - `claude/engineering-debt` (worktree `.claude/worktrees/engineering-debt`)
    — 9 commits of tooling/infra fixes. **Ready for review and merge.**
  - `claude/store-provenance` (worktree `.claude/worktrees/store-provenance`)
    — the WIP refactor snapshot + recursion-bounding fixes. **Not ready for
    master** (see below).
  - `claude/code-review-design-issues-763cd1`, `worktree-claude`,
    `codex/click-expand`, `wip/tactic-certificates-2026-07-18` — older or
    inactive; audit before deleting.
  - Stale detached worktrees under `/private/tmp` (`click-head-audit`,
    `click-head-probe`, `click-p0-baseline`) — cleanup candidates via
    `git worktree remove`.

## Work stream 1: design review (done, findings only)

A full design review produced a ranked issue list, saved verbatim in
`design-review.md` (same directory as this file). The top soundness items
(theorem-forging kernel APIs, unguarded ∀-generalization, ABI divergence)
were already fixed on master by another agent. Still-open findings, ranked:

1. **Kernel Click leaks into user proofs** — examples use undocumented
   spellings (`load_int32(...)`, `owner[0..4]` for a pointer field).
2. **Write-only proofs** — exact-spelling fact matching, positional
   `statement(5)`/`requirement 0` indices, order-sensitive one-shot closers.
3. **Verbosity** — ~5:1 spec:code, no fact-set abbreviations, no
   imports/modules (stdlib lemmas copy-pasted per file), no frame rule for
   composite-resource `fold`.
4. **Three overlapping memory-concept families** — `loadable` vs resource
   verbs vs effects clauses; byte vs element units (`loadable(p, 12)` vs
   `p[0..n]`); `owns` vs `consumes`+`produces`; `mutable_field`
   undocumented.
5. **No source spans in ClickError** (C0 and Click parse errors now carry
   line/column on the engineering-debt branch, but ClickError generally is
   still a bare string) and a shadow lexer in expansion.rs re-derives
   positions.
6. **proof.rs is a 20k-line monolith**; ~3,000 lines of near-duplicate
   evaluators across checking/lowering/proof; 13-arg function signatures.
7. **Term representation embeds full CMemory snapshots** — every deep
   comparison is O(memory), prover scans multiply it; this is the root
   cause of the store-provenance perf pathology below. Hash-consing or
   memory IDs is the structural cure.
8. **Thread-local fuel nondeterminism** in simp (`SIMP_REASONING_FUEL`).

Concrete design proposals for items 2–4 are in `language-proposals.md`
(same directory as this file) — match-modulo-normalization for tactics,
labels over positional indices, two-phase grouped closers, imports →
factsets → parameterized resources → fold-modulo-frame, and collapsing the
memory families onto resource verbs with element-only units.

## Work stream 2: `claude/engineering-debt` (ready)

Nine commits, all validated:

- Line/column positions in C0 and Click parse errors; human-readable token
  spellings (no more `expected Semicolon, got PlusPlus` or `at token 37`).
- Typed `expansion_complete` flag on ClickError replacing the
  sentinel-message-string control flow in proof.rs.
- Replay-loop perf: branch skeleton no longer rebuilt per tactic; removed a
  per-Transport CState clone.
- New `src/cli.rs`: shared (previously 4x-duplicated, drifted) helpers for
  source locations, durations, child-process watchdogs, project discovery.
- `click-verify file.click` whole-file mode + uniform `--help` across all
  four binaries.
- `click-audit` now enforces todo.md checklist steps 6–7 (fresh whole-file
  reverification of rewrites; byte-identical re-expansion). Step 8 is
  marked unimplemented in a comment.
- Parallel mdtest/examples harness: bounded worker pool, collects ALL
  failures (full 269-file suite: ~47s wall vs 15+ min serial).

Validation: 268/269 mdtests pass; the one failure
(`witness_and_choose.md`) reproduces at base `cce4e3d` — a pre-existing
master regression, worth flagging separately. Full `cargo test --lib` has a
60+ CPU-minute tail of giant proof tests (pre-existing; see "slow tests").

## Work stream 3: `claude/store-provenance` (functional, not mergeable)

Context: symbolic execution dropped a cached `data[len-1] = 0` store when
a later `owner->len` store occurred despite explicitly separated ranges.
The prior agent's refactor moves certified store provenance onto
`ExecutionPureFact` (kernel-private, NOT exposed as a generic Proposition).
Their WIP stack-overflowed in
`explicit_store_step_with_unfolded_resource_facts_verifies`.

The branch's second commit fixes the pathology:

- Depth is threaded through the assumptions.rs disjointness/in-range/
  containment helpers (they previously re-entered through depth-0 wrappers,
  so `MEMORY_RESOLUTION_ALIAS_DEPTH_LIMIT` never bound anything).
- Two per-query node budgets (`MEMORY_RESOLUTION_NODE_BUDGET` = 8000,
  `RESOURCE_PROVER_NODE_BUDGET` = 5000 in reasoning.rs) bound total work.
  **These constants are tuned empirically, not principled** — exhaustion
  makes a true fact unprovable (soundness-safe, but a confusing "missing
  pure fact" failure). If a proof mysteriously fails, suspect fuel first.
- `memories_match_for_pointer_load_under_assumptions` uses only the
  bounded distinctness check while inside a condition decision
  (`inside_condition_decision()`), breaking a decide → order-facts →
  memory-load-equality → distinctness → decide cycle.

Status: both target tests pass (`expanded_read_step_keeps_...` ~34s,
`explicit_store_step_...` ~22s, formerly a stack overflow);
`kernel::tests` 182/182. **Still failing — pre-existing at the WIP
baseline, i.e. the unfinished part of the refactor**: mdtests matching
`composite_resource_owner_buffer_hidden_separate_projection`,
`separate_symbolic`, `composite_resource_separate`, `permission_call`,
`resource_summary`.

To finish: make those five groups pass on this branch, run the FULL mdtest
+ examples suites, then land the whole thing as one change. Do not land
with those groups red — that would regress master to unblock two tests.

## Slow-test ledger (act on this)

- Both store-provenance target tests are 20-35s *when healthy* — already
  too slow; prover regressions manifest as hangs, not failures.
- `cargo test --lib` has single tests requiring tens of CPU-minutes.
- `examples/owned-string` fails whole-file verification on master
  ("exact symbolic execution produced no valid paths") — pre-existing.
- Recommendation (repo owner agrees): enforce a hard per-test time limit
  (e.g. cargo-nextest `slow-timeout` with terminate, or a watchdog like
  the mdtest harness's 30s). Treat any test >10s as a bug. Do this BEFORE
  merging the store-provenance work.

## Suggested priority order

1. Merge `claude/engineering-debt` into master (review first; it's
   self-contained and validated).
2. Add the per-test time budget to the lib suite.
3. Finish the store-provenance refactor on its branch (five failing mdtest
   groups), full suite green, then merge.
4. File/fix the two pre-existing master failures (`witness_and_choose.md`,
   `examples/owned-string`).
5. Term representation (hash-consing / memory IDs) — the structural cure
   for the prover blowups; big, do it as its own project.
6. Language-design proposals in `language-proposals.md` — discuss with the
   repo owner before implementing.

## Conventions observed in this repo

- Only humans edit README.md above the marked line.
- Behavior changes land with an mdtest and doc update in the same change.
- `Theorem` construction stays inside `src/kernel/`; don't add public
  kernel endpoints that mint theorems from caller-supplied conclusions.
- Verify with `cargo test --test mdtests` (fast, on the engineering-debt
  harness) rather than the full lib suite while iterating.
