# Repo hygiene (needs owner sign-off before deletions)

Status: blocked (deletions need the owner)
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
