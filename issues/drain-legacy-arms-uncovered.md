# Drain legacy arms are corpus-invisible

## Violated invariant

Every feature-live drain arm should be exercised by at least one fixture,
so behavioral changes to it are caught by `scripts/check.sh` rather than
discovered by probes. An instrumented run of the full lib suite and both
fixture gates (2026-08-18, master ~e7d77a45) hit none of the nine legacy
working-set mutation sites in `src/lang/click/proof/claim_proofs.rs`. Six
are no-goal fallback arms with live goal-based twins (slated for deletion
by the working-set inversion plan in `issues/proof-object-api.md`), but
three are the sole implementations of their tactic kinds and stay:

- the two resource-projection arms (`FoldResource` / `CloseOpen` at
  function exit, via `project_outcome_resource_facts`), and
- the region-frame certifier arm, plus the `Simp` legacy-planner escape.

These are reachable by real Click programs (fold-at-exit sidecars) but no
mdtest or example currently drives them, so the inversion work cannot see
regressions in them.

## Intended regression

One small mdtest whose claim folds a composite resource at function exit
(driving `PostExecutionTactic::FoldResource` through the drain's
projection arm), and one driving the region-frame certifier. Each should
pin the resulting certificate shape, not merely verification success.

## Findings (2026-08-18, corrected)

An initial probe run concluded the legacy arms were corpus-unreachable
and the smart drivers subsumed fold-at-exit; both conclusions were
capture artifacts (`cargo test` swallows output on passing tests —
probes must panic or run under `--nocapture`). Corrected findings:

- The grouped fold-at-exit fixture
  (`mdtests/post_execution_fold_projects_outcome.md`) routes through
  `replay_linear_tactics` — the terminal-effect fast path declines
  scripts not ending in a frame — defers the fold, and drives the
  drain's `Fold` projection arm (confirmed twice per run under
  `--nocapture`). The fold-at-exit coverage criterion is met.
- The deleted no-goal fallback arms are genuinely unreachable in the
  corpus: they are hard errors now and the full gates stay green.
- Still uncovered: the region-frame certifier arm and the `CloseOpen`
  projection arm; each needs its own fixture the same way.

## Acceptance criteria

- Running the reachability probe (temporary `eprintln!` at each remaining
  legacy mutation site) over `scripts/check.sh` shows at least one hit in
  each surviving arm.
- The new mdtests fail if the projection or region-frame arm mis-handles
  the working set (e.g., drops the re-import into the outcome goal).
- The issue file and its Open-list line are deleted when the coverage
  lands or when the arms themselves are deleted by the inversion.
