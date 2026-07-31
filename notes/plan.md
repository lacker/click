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
| split-buffer-perf.md | done | Audit at 0 SLOW: constant test hoisted above the equality search; transport equality memoized |
| one-gateway-check.md | done | Audit done: mid-execution gated by replay_smart_plan; 3 bypasses in the ungrouped post-execution drain (39 corpus hits) — see file for follow-up tasks |
| cli-consolidation.md | done | Helpers single-sourced in src/cli.rs; click-verify DIR mode + docs; click timing: drift is now a loud error or a counted warning |
| proof-panics.md | done | 78 sites classified; 7 converted, 71 invariant-true; the design review's cited example is a false positive |
| while-invariant-rule.md | done | Fenced: rule is `#[cfg(test)] pub(super)`, no callers; a sound fix needs `CLoopInvariantCheck`, not a flat `Vec<Proposition>` |
| docs-vocabulary-pass.md | done | Inventory + synonyms documented; audit docs match the binary (worktree-agent-ae547bd447d583266) |
| parser-ergonomics.md | done | Both stale: `a->b->c` verifies (new mdtest), else already optional; 22 no-op else paddings removed; doubly-indirect `owns` parked as C5 |
| lib-ignored-expansion-tests.md | done | Premise policy fixed: 5 of 7 un-ignored. Certificates now carry consumed conditions + non-reconstructible permissions. Found a latent `condition_polarity_equivalent` None==None bug, filed separately |
| certificate-gateway-bypasses.md | open | Redesign accepted; all three bypasses now lower to certificates. Strict-gate worklist 24 -> 0 (predicate/unfolded-body spellings; proof_advance_pointer_local's proof rewritten to name its local). Next: owner flips the gate default, then the ClosedClaim restructure |
| store-provenance-family.md | parked | owned-string, owned-vector, 6 mdtests — blocked on the canonical-memory arc |
| named-memory-states-arc.md | open | The canonical-memory representation change: memory states named in a derivation DAG instead of embedded as values. Staged behind `CLICK_DISABLE_MEMORY_DAG`; unparks store-provenance-family. Stages 1, 2, 2a landed — `old(...)` now names function entry instead of resolving positionally, un-ignoring `verifies_old_memory_loop_invariant` and de-quarantining `fill_tail_keeps_first`. Every remaining corpus member now fails in the invariant closer (stage 3) |
| condition-polarity-none-equivalence.md | done | Predicate sound (both sides need a canonical order form) + proof-backed snapshot bridge at four sites. input-cursor/owned-split-buffer sidecars regenerated (their premises were false); owned-segmented-buffer needed the transport source+target bridges. All four gates green |
| repo-hygiene.md | done | Executed with owner approval; worktree-claude verified (all 3 fixes on master via rebase-copy cd90c80) and deleted |

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
