# Enforce smart-tactic deadlines inside verification

## Problem

The fixture harness and profiler can report that a smart tactic exceeded the
two-second budget, but ordinary verification lets the tactic continue until it
finishes or an outer project process is killed. During owned-vector growth, a
broad `execute()` search ran for tens of seconds and the next useful failure was
only visible after a roughly one-minute project run.

Post-hoc timing is not a tactic budget. A smart tactic that cannot find a
certificate promptly should stop at that tactic and report a bounded search
failure. Continuing makes proof development slow and lets one search consume an
entire project deadline.

## Intended design

- Give every smart tactic an in-process wall-clock deadline matching the
  default smart budget, currently two seconds.
- Check the deadline at all potentially unbounded search boundaries, not only
  at the top-level tactic dispatcher. Kernel work that cannot cheaply poll must
  receive a cancellation/deadline token at its existing budget checkpoints.
- Return a structured error naming the tactic, source location, class, elapsed
  time, and limit.
- Keep `click-profile`'s outer project limit as crash/hang containment, not the
  normal way a slow tactic stops.
- Permit an explicit diagnostic override for reduction work, while the default
  tests and verifier keep the production bound.

## Regression

Add a focused fixture containing a deliberately explosive `execute()` search.
Invoke the same verification entry point used by `click-verify`, not merely the
isolated test harness. Assert that it fails at the selected smart tactic within
a small tolerance and that later tactics are not entered.

Also cover nested smart work inside `have` and control tactics so exclusive-time
accounting cannot bypass the active deadline.

## Acceptance criteria

- Ordinary verification stops an over-budget smart tactic locally.
- The default failure arrives near the tactic budget, not the project budget.
- Profile timing classifies the stopped operation as failed SMART search.
- Simple certificate replay and control containers retain their own independent
  limits.
- Documentation no longer implies that post-hoc harness inspection is the
  enforcement mechanism.
