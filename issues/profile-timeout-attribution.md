# Attribute active work when profiling times out

## Problem

After removing the failing growth proof, `click-profile --time-limit 30s
examples/owned-vector` reached its project deadline with no tactic over a class
budget. It labeled the project `HEALTHY VOLUME`, but attributed roughly twenty
seconds to `PROCESS/DRIVER` and had only completed part of the sidecar.

A timeout is not a healthy completed profile. If verifier work is still active,
the report must identify that phase or tactic. Large residual driver time hides
the actual bottleneck and gives the wrong next action.

## Intended design

- On timeout, capture the currently active frontend, environment, tactic,
  certification, or verifier-core span.
- Charge observed child wall time through interruption to that active span, or
  report it explicitly as interrupted work rather than process/driver overhead.
- Reserve process/driver for measured parent orchestration after child phase
  accounting, not unknown verifier execution.
- Never emit `HEALTHY VOLUME` as the sole diagnosis for an incomplete project.
  State what was incomplete and direct the user to the active operation.

## Regression

Run a deterministic child fixture that begins a named smart, simple,
certification, and verifier-core span before blocking. Interrupt each form and
assert that the profile names the active span, preserves completed exclusive
timings, and keeps process/driver residual small and explainable.

## Acceptance criteria

- Every timed-out profile names or classifies the active work.
- Interrupted time is not silently assigned to process/driver.
- An incomplete project cannot receive an unqualified healthy diagnosis.
- The report's next action follows the active class or phase.
- The command exits unsuccessfully on timeout after its complete child process
  group has been terminated; process cleanup itself is tracked separately in
  `bounded-runs-leave-orphan-verifiers.md`.
