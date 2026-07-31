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
- worktree-claude branch — contains one unmerged commit "Fix three
  megakernel soundness holes (havoc, overflow, fold split)" against an
  old tree layout (src/megakernel.rs, pre-refactor). Almost certainly
  re-landed during the kernel split, but soundness fixes do not get
  deleted on "almost certainly": verify each of the three fixes exists
  on master, then delete. Small archaeology task for anyone.
- The two live agent worktrees/branches and the active session branch.
