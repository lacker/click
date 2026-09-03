# Keep composite resource-member verification within the slow-test budget

## Status

Filed 2026-09-03 after the default nextest run reported
`composite_definition_members_scale_near_linearly` as slow. The test passes
on current master, but takes about 40 seconds there and about 52 seconds on
the allocation follow-up branch, crossing the repository's 10-second slow
threshold and leaving little margin before its 60-second timeout.

## Violated invariant

The verifier's simple work must scale with the selected resource definition
and remain prompt. A deterministic near-linear work assertion is not enough
if the implementation spends tens of seconds executing the four sample
projects: nextest's slow-test report is an early warning for the same
tooling-health failure that can become a timeout under ordinary load.

## Intended regression

Run:

```sh
cargo nextest run --lib composite_definition_members_scale_near_linearly
```

The existing fixture in `src/surface/tests/scaling_tests.rs` should continue
to verify resource definitions with 8, 16, 32, and 64 members, retain its
near-linear deterministic-work assertion, and finish within the default
nextest slow-test budget without a `SLOW` or `TIMEOUT` report.

## Acceptance criteria

- Identify and reduce the verifier or fixture overhead responsible for the
  composite resource-member curve; do not raise nextest's timeout or remove
  the scaling assertion.
- The focused nextest test completes without a slow-test report on the
  repository's supported development environment.
- `scripts/check.sh` passes without any slow or timed-out Rust tests, and the
  mdtest and example gates remain green.
- The deterministic work curve remains near-linear at all four existing
  sizes, with no proof-only C changes or weakened resource checks.
