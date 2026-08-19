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

## Finding (2026-08-18)

A fold-at-exit fixture (`mdtests/post_execution_fold_projects_outcome.md`,
grouped contract with `execute(); fold(...); simp()`) verifies entirely
through the Proof-based drivers with zero deferrals: the legacy
`tactic_replay` executor never runs, so the drain's `Fold` projection arm
is unreachable by any script shape the smart drivers accept. The
surviving legacy arms are therefore reachable only through scripts the
smart drivers decline; establishing which declining shapes are
user-expressible (and pinning one per arm) — or proving driver
subsumption — is what stands between the arms and deletion.

## Finding 2 (2026-08-18)

The grouped fixture's `fold(...)` is load-bearing (removing it fails the
claim) yet applies through none of `Proof::apply_step`,
`apply_step_at`, or `apply_step_with_origin` at exit, defers nothing,
and never enters the legacy `tactic_replay` fold handler. The remaining
candidate is the post-execution exit planner consuming the script's fold
during `simp` planning (the same planner behind the drain's `Simp`
escape). Tracing that route is the prerequisite for judging whether the
drain's `Fold` arm and the `Simp` escape are one shared surface or two.

## Acceptance criteria

- Running the reachability probe (temporary `eprintln!` at each remaining
  legacy mutation site) over `scripts/check.sh` shows at least one hit in
  each surviving arm.
- The new mdtests fail if the projection or region-frame arm mis-handles
  the working set (e.g., drops the re-import into the outcome goal).
- The issue file and its Open-list line are deleted when the coverage
  lands or when the arms themselves are deleted by the inversion.
