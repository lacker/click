# Owned-split-buffer verification exceeds the slow-test threshold

The unchanged C project verifies successfully, but two warm focused example
gate runs took 11.53s and 14.50s:

```sh
CLICK_EXAMPLE=owned-split-buffer cargo test --test examples -- --nocapture
```

Ordinary direct CLI verification took roughly 5.5s to 6.4s in the same work
session. No tactic or project deadline failed. The large CLI/test-harness gap
suggests test-mode deterministic work or cache behavior that should be
attributed rather than hidden by raising the documented 10-second threshold.

## Regression design

Profile the unchanged project through both the ordinary CLI and the focused
example gate. Attribute time to proof sites and non-tactic phases, including
standard-library setup and any behavior enabled only in the test build. Keep
the existing C and Click proof as the regression.

## Acceptance criteria

- The focused example gate verifies comfortably below 10 seconds on the normal
  development workflow.
- CLI and harness timing differences are explained and reduced where they
  represent duplicate deterministic work.
- No tactic, project, or test budget is raised.
- No C source, claim, or example structure is weakened or reshaped.
