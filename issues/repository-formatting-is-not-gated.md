# Repository formatting is not gated

`cargo fmt --check` fails on the current tree, so formatting drift
accumulates and every agent inherits diffs it did not create. The CI
workflow deliberately omitted a formatting step when it was introduced,
because gating on a red check would have trained everyone to ignore CI.

The invariant: the gate should include formatting so local and CI judgments
match and drift cannot accumulate. The regression is the check itself.

## Acceptance criteria

- One commit formats the repository (`cargo fmt`), coordinated so it does
  not collide with concurrent agents' in-flight work.
- `scripts/check.sh` runs `cargo fmt --check` before the test suites, so
  the same command gates locally and in CI.
- The gate stays green.
