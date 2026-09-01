# Fix the incremental verification marker and cache key

Found by the 2026-09-01 kernel audit at cb034b21. Exit-status aggregation
in `click verify` was traced and is sound (every per-sidecar and
per-function result is `?`-propagated to `main`); the two defects below are
in the skip logic.

- `click verify --changed-since <rev>` falls back to a full rebuild when
  `<rev>` has no marker, then records the marker for HEAD only
  (`record_full_verification` at `src/bin/click-verify.rs:243` uses
  `git_commit_id(&repo, "HEAD")` at `:433`). Unless HEAD equals `rev`, the
  next `--changed-since <rev>` run rebuilds again, so incremental mode only
  ever amortizes against the previous HEAD.
- The marker hashes the binary, the commit, and the sidecar path
  (`marker_contents`, `click-verify.rs:401-410`) but not the environment
  variables that change verifier behavior: `CLICK_DISABLE_TACTIC_BUDGETS`,
  `CLICK_DISABLE_CERT_ARMS`, `CLICK_DISABLE_MEMORY_DAG`,
  `CLICK_DISABLE_DECIDE_MEMO` (`src/instrumentation.rs:362`;
  `src/kernel/api/contract_certification.rs:2303-2330`;
  `src/kernel/primitives.rs:1141`; `src/kernel/assumptions.rs:640`). A
  baseline attested with budgets disabled is reused by later runs with them
  enabled.

## Violated invariant

A cached "verified" result may be reused only when every input that
determines the verdict is unchanged: sources, sidecars, the binary, and the
configuration the binary ran under. The marker must be recorded for the
baseline the user asked to compare against.

## Intended regression

Two tests in the `mod tests` block of `src/bin/click-verify.rs` (line 610): after a full rebuild triggered
by a missing marker for `rev`, a second `--changed-since rev` run with no
source changes skips unchanged sidecars; a marker written with
`CLICK_DISABLE_TACTIC_BUDGETS` set is not honored by a run without it.

## Acceptance criteria

- The marker is recorded for the requested baseline (and HEAD when they
  differ), and the environment switches are part of `marker_contents`.
- The two tests pass; `scripts/check.sh` passes.
