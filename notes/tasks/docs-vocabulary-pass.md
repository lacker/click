# Docs vocabulary pass

Status: in progress
Claimed: worktree-agent-ae547bd447d583266, 2026-07-30

Scope (design-review honorable mention): one documentation pass over
docs/ fixing tactic-vocabulary churn:
- "execute_rest() is legacy spelling for execute_rest()"
  self-reference (separation-logic.md:265 at review time).
- close_invariants() used in examples but missing from the tactic
  inventory.
- ~30 tactics with near-synonym clusters
  (step/execute_step/execute_until/execute_rest/...) — document the
  canonical set and mark the synonyms.
- While in there: confirm docs/advanced/testing-click.md reflects the
  2026-07-30 click-audit behavior (slow-site limit, run time limit,
  once-per-claim cold reverify, claim-based fixed point).

Done when: the tactic inventory is complete and self-consistent and the
audit docs match the binary's USAGE text.
