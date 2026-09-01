# Enforce branch-join lineage and evidence-prefix invariants in release builds

Found by the 2026-09-01 kernel audit at cb034b21. No untrusted-input path
reaches a wrong-lineage join today; every caller was traced and found to
construct arms as clones of the parent. The invariants are nonetheless
enforced only by `debug_assert!`, which is compiled out of release-profile
builds. `Cargo.toml` sets no profile overrides and nothing in `scripts/`,
`docs/`, or `.github/` builds with `--release`, so every existing gate runs
with the assertions on and none exercises the release behavior; a release
build of the CLI would run without them. No test asserts that a bad join is
rejected.

- `src/kernel/proof/branches.rs:236-270` holds the only child/parent lineage
  checks for frontier joins (children open or reserved by this lineage,
  parent retired), all as `debug_assert!`. `publish_checked_frontier_join_inner`
  (`src/kernel/proof/object.rs:1333-1394`) checks only
  `has_allocated(child)` in reserved mode or `get(child).is_some()`
  otherwise, plus parent allocated-and-not-open; it never receives the
  `SplitId`, unlike `join_closed_split` (`object.rs:449`). `join_reserved_at`
  (`branches.rs:255-277`) removes each child behind a `debug_assert!` only.
- `SharedVec::suffix_since` (`src/kernel/proof/storage.rs:53-66`) checks the
  shared prefix element-wise only under `debug_assert!`; in release,
  `arm_effect_deltas_are_exact` (`src/kernel/proof/execution.rs:1130-1140`)
  therefore only checks `arm.len() >= parent.len()` and compares the tail.
- The other proof-machinery `debug_assert!`s (`branches.rs:122-197`,
  `execution.rs:1959-1980`, `src/kernel/primitives/resource_algebra.rs:845-860`)
  were traced to callers that guarantee the precondition; they may stay as
  they are but should be listed in the audit that closes this issue.

## Violated invariant

A frontier join may close a split only when every child arm of that exact
split is represented, each arm descends from the parent trace, and the check
that establishes this runs in every build that can produce a verified
verdict.

## Intended regression

Kernel unit tests, run in release configuration as well as debug:

1. A frontier join supplied with one arm of a two-arm split, or with an arm
   allocated under a different split, is rejected with an error, not a panic
   and not success.
2. `arm_effect_deltas_are_exact` with an arm whose effect list has the
   parent's length but different prefix content returns false.

## Acceptance criteria

- The lineage checks in `branches.rs:236-270` become real checks that return
  `Err` on violation, and the frontier join API takes the `SplitId` and
  verifies every child belongs to it.
- `suffix_since` verifies prefix equality in all builds, or
  `arm_effect_deltas_are_exact` verifies it independently.
- The two tests above; the test suite includes at least one release-profile
  run of them (or the checks are plain `assert!`/`Err` so profile is
  irrelevant).
- `scripts/check.sh` passes.
