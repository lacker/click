# Bound ordinary `click-verify` runs

## Problem

`click-profile`, fixture harnesses, expansion, and audit have outer wall-clock
limits, but direct `click-verify` has no project/proof-unit time-limit option. A
slow certification or verifier-core phase can therefore run indefinitely even
after tactic deadlines are enforced. Several owned-vector commands had to be
interrupted manually while diagnosing growth.

## Intended design

- Give `click-verify` a documented default wall-clock limit and a
  `--time-limit` override using the same duration parser as the other tools.
- Bound each project independently when a directory is verified, and name the
  active sidecar/proof unit on timeout.
- Emit phase progress so a non-tactic timeout distinguishes frontend,
  environment, certification, verifier core, and driver work.
- Exit unsuccessfully on timeout.
- Use the shared bounded-run process-group cleanup so no verifier survives the
  command.

The outer limit is containment, not a replacement for per-tactic deadlines or
performance fixes. A project that repeatedly approaches the limit still needs a
focused issue.

## Regression

Add CLI tests around a deliberately blocked proof-unit worker and a directory
containing one fast and one blocked sidecar. Assert bounded failure, project
identification, nonzero status, process cleanup, and successful override parsing.

## Acceptance criteria

- Direct sidecar, selected proof-unit, project, and examples-directory modes are
  all bounded.
- Timeout diagnostics name active phase and target.
- The command returns nonzero and leaves no child processes.
- Fast verification behavior and output remain unchanged.
