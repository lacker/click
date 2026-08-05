# Enforce tactic deadlines inside verification

## Problem

The fixture harness can report that a completed tactic exceeded its class
budget, but ordinary verification lets the tactic continue until it finishes or
an outer process is killed. During owned-vector growth, broad `execute()` search
ran for tens of seconds before the next failure became visible. The same gap
applies to deterministic SIMPLE replay and CONTROL-container overhead: their
budgets are inspected after completion rather than enforced while running.

Post-hoc timing is not a tactic deadline. An over-budget tactic should stop at
that tactic and report a bounded failure; it should not consume an entire
project deadline or leave the user wondering whether verification is hung.

## Intended design

- Give every tactic an in-process deadline based on its verifier-emitted class:
  500ms SIMPLE, 2s SMART, and 2s CONTROL by current defaults.
- Check the deadline at all potentially expensive boundaries, not only the
  top-level dispatcher. Kernel work should receive a cancellation/deadline token
  through its existing execution-budget checkpoints.
- Preserve exclusive accounting for nested tactics: a control container does
  not inherit child time, but its own unclassified work remains bounded.
- Return a structured error naming the tactic, location, class, elapsed time,
  and limit.
- A stopped SMART search has no certificate and is a reducible Click bug. A
  stopped SIMPLE or CONTROL operation is an engine bug and must not be expanded.
- Permit an explicit diagnostic override for reduction work while default
  verification and tests retain production limits.

## Regression

Add focused fixtures for deliberately expensive SMART search, SIMPLE replay,
and CONTROL-only overhead. Invoke the ordinary verification API, not merely the
isolated harness. Assert that each stops near its class deadline, later tactics
are not entered, and nested accounting chooses the active class correctly.

Include an `execute()` case because it was the concrete failure that exposed
this gap.

## Acceptance criteria

- Ordinary verification stops every over-budget tactic locally.
- Failures arrive near the class budget rather than the project budget.
- Profile timing classifies interrupted work consistently with verification.
- Cancellation leaves proof state unchanged and does not leak workers.
- Documentation distinguishes in-process enforcement from outer crash/hang
  containment.
