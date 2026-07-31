# Plan — status board

Last updated: 2026-07-30 (evening). Read `conventions.md` before
working; each task lives in its own self-contained file under `tasks/`
so different agents can work different rows without colliding. Claim a
task by setting the `Claimed:` line in its file.

Baseline: **master is green** on all three gates (lib 465, mdtests,
examples — see conventions.md for the commands). The 2026-07-30
sessions landed the decide memo (~200x on hot proofs), six
certifier/kernel fixes, three example de-quarantines (input-cursor,
owned-segmented-buffer, owned-split-buffer), and a usable bounded
click-audit (full run 314 s, 98 sites passing).

## Board

| Task file (tasks/) | Status | One-line scope |
|---|---|---|
| split-buffer-perf.md | open | Kill the last 2 SLOW audit findings (~7.7 s unit; 3.6 s contract execution) |
| one-gateway-check.md | open | Bounded code audit: every smart success routes through TacticCertificate replay |
| cli-consolidation.md | done | Helpers single-sourced in src/cli.rs; click-verify DIR mode + docs; click timing: drift is now a loud error or a counted warning |
| proof-panics.md | done | 78 sites classified; 7 converted, 71 invariant-true; the design review's cited example is a false positive |
| while-invariant-rule.md | done | Fenced: rule is `#[cfg(test)] pub(super)`, no callers; a sound fix needs `CLoopInvariantCheck`, not a flat `Vec<Proposition>` |
| docs-vocabulary-pass.md | done | Inventory + synonyms documented; audit docs match the binary (worktree-agent-ae547bd447d583266) |
| parser-ergonomics.md | open | required-else and a->b->c chains: fix small or park with writeup |
| lib-ignored-expansion-tests.md | open | Retest 7 #[ignore] lib tests; un-ignore or diagnose |
| store-provenance-family.md | parked | owned-string, owned-vector, 6 mdtests — blocked on the canonical-memory arc |
| repo-hygiene.md | blocked | Stale branches/worktrees/stash — deletions need the owner |

## Reference docs

- `conventions.md` — gates, multi-agent workflow, decision boundaries,
  working rules, settled invariants, tooling flags. Read first.
- `canonical-memory.md` — the named-memory-states arc (the intended fix
  for the store-provenance family). Larger than short-term; owner-gated.
- `design-review.md` — the ranked 2026-07 review (historical reference;
  actionable residue is in tasks/).
- `language-proposals.md` — surface-language proposals (parked; any of
  these is a Surface Click semantics change and needs the owner).

## Done criteria for the current arc

The profile/expand/audit ladder is done when the full audit reports
zero site failures on the green corpus (only split-buffer-perf.md
remains) and the profile stays clean (currently: no SIMPLE >500 ms, no
SMART >2 s in any verifying project).
