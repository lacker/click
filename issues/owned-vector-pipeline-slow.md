# Reduce the owned-vector pipeline verification time

## Problem

With stale verifier workers removed, a clean project profile completes in about
18.5 seconds. It reports no tactic above its class threshold, but spends about
11 seconds in certification and 4.9 seconds in verifier core. Certification is
roughly 315ms per claim and 1.1s per path, above the documented development
baselines. This violates the repository rule that unexpectedly slow
verification must be investigated before feature work continues.

The project is quarantined from the default examples sweep while this issue is
open. The new general push proof lives in the separate, fast `vector-push`
project so quarantine does not hide new coverage.

## Investigation order

1. Compare the current kernel with commit `ad25866` to determine whether the
   runtime-allocation work regressed an unchanged pipeline proof or merely
   exposed pre-existing certification cost.
2. Profile certification paths and identify repeated exact-execution,
   equivalence, or resource-replay work. Tactic expansion is not indicated by
   the clean profile.
3. Check whether the proof unit is repeatedly reconstructing its function
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
- A 30-second profile remains complete and accounts for the entire project.
- The owned-vector quarantine entry is removed in the same change.
- The fix does not regress the independently fast `vector-push` or
  `runtime-int32-allocation` projects.
