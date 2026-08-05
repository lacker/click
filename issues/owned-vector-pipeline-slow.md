# Reduce the owned-vector pipeline verification time

## Problem

Targeted verification of `vector_pipeline` takes about 52 seconds. A 30-second
profile reaches the deadline after completing the preceding functions, reports
no individual tactic above its class threshold, and attributes most remaining
time to process/driver. This violates the repository rule that unexpectedly
slow verification must fail locally and be investigated before feature work
continues.

The project is quarantined from the default examples sweep while this issue is
open. The new general push proof lives in the separate, fast `vector-push`
project so quarantine does not hide new coverage.

## Investigation order

1. Compare the current kernel with commit `ad25866` to determine whether the
   runtime-allocation work regressed an unchanged pipeline proof or merely
   exposed pre-existing cost.
2. Fix profile timeout attribution first enough to identify the active phase.
3. If one smart tactic is responsible, require the new local smart deadline to
   stop it and reduce that search. If deterministic replay or certification is
   responsible, optimize the engine path rather than expanding arbitrary smart
   tactics.
4. Check whether the proof unit is repeatedly reconstructing its function
   environment or certifying the same dependency graph.

Do not “fix” this by increasing project limits, deleting the composition
example, or splitting one proof into files solely to hide aggregate work.

## Regression

Add a timing-oriented test around targeted `vector_pipeline` verification after
the cause is reduced. It should assert the relevant operation count or bounded
engine budget where possible; wall-clock comparison may remain a coarse outer
guard.

## Acceptance criteria

- Targeted `vector_pipeline` verification completes below the normal ten-second
  slow-test threshold on the development baseline.
- No smart, simple, or control tactic crosses its class budget.
- A 30-second profile completes and accounts for the entire project.
- The owned-vector quarantine entry is removed in the same change.
- The fix does not regress the independently fast `vector-push` or
  `runtime-int32-allocation` projects.
