# Binary-tree verification exceeds the slow-test threshold

The focused example gate for `examples/binary-tree` verifies successfully but
took 11.27 seconds in a warm debug test run:

```sh
CLICK_EXAMPLE=binary-tree cargo test --test examples -- --nocapture
```

That crosses the documented 10-second slow-test threshold. No individual
tactic budget failed, and the `simp() using` foundation change did not alter
the example proof, so this is a separately tracked baseline performance
problem rather than permission to reshape the example or raise a limit.

## Regression design

Profile a verified binary-tree run with the ordinary CLI and attribute the
project time to proof sites and non-tactic phases. Preserve the existing C and
Click proof as the regression. If no individual tactic is slow, reduce the
aggregate verifier phase responsible for the repeated work.

## Acceptance criteria

- The unchanged binary-tree project verifies comfortably below the 10-second
  slow-test threshold on the normal development workflow.
- No tactic, project, or test budget is raised.
- No C source, claim, or example structure is weakened or reshaped.
- Any optimization has a focused deterministic-work or cache-behavior
  regression where practical.
