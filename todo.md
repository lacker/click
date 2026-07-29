# Finish `click-profile` / `click-expand` / `click-audit`

Last reviewed: 2026-07-28

## Objective

Finish the proof-performance workflow so it can be used routinely without
special context:

1. `click-profile` identifies the next actionable slow proof step.
2. Slow simple tactics are fixed in the verifier.
3. Slow smart tactics are replaced by their accepted `TacticCertificate`.
4. `click-audit` checks every smart source site by expanding, reverifying, and
   checking idempotence.

The work is complete when the examples are fast enough to run regularly and a
full audit passes. Performance work is also correctness work here: a command
that routinely exceeds its watchdog cannot provide a dependable audit.

## Settled design

These are invariants, not remaining tasks:

- `TacticCertificate` is the smart/simple boundary. A successful smart tactic
  must replay through a surface-expressible certificate before its result is
  accepted.
- Expansion emits that exact accepted certificate. It does not search for a
  second proof and does not use a generic fallback.
- Simple tactics are deterministic replay and must be fast. Do not hide a slow
  simple tactic by expanding an enclosing smart tactic.
- `ProofSite` and one-based `PATH:LINE:COLUMN` locations are shared by
  verification, profiling, expansion, auditing, and source rewriting.
- `click-expand` emits a rewritten sidecar and does not independently reverify
  it. Verification and auditing are separate composable operations.
- `click-verify PATH:LINE:COLUMN` verifies the containing semantic unit and its
  transitive C-call dependencies.
- Kernel Click is an internal Rust representation with no textual syntax.
  Source, diagnostics, profiler hints, and expansion output are documented
  Surface Click accepted by the ordinary parser.
- Canonical struct spellings are `owner->field`,
  `(owner->pointer_field)[start..end]`, and `object(owner)`. Low-level
  `load_*` and `byte_offset` forms are documented Surface Click escape hatches
  only when source provenance is unavailable.
- CLI watchdogs must kill and reap their children.

## Tooling already present

- `click-profile` classifies timings as `SIMPLE`, `SMART`, or `CONTROL` and
  defaults to 500 ms / 2 s / 2 s thresholds.
- `click-expand [--time-limit DURATION] PATH:LINE:COLUMN` selects explicit,
  nested, grouped, omitted, loop-phase, and structural proof sites.
- `click-verify PATH:LINE:COLUMN` performs location-targeted verification.
- `click-audit` inventories sites syntactically, uses reusable per-file
  sessions, has separate session/expansion/verification watchdogs, and resumes
  inclusively with `--start-at`.
- The audit checks that rewriting is localized, the rewritten unit verifies,
  and re-expansion is byte-identical.

Current evidence:

- all 249 current smart sites inventory and parse as Surface Click;
- all binary-tool tests pass: 9 audit, 3 expand, 7 profile, and 1 verify;
- the 50 parser tests and 14 focused surface/certificate tests pass;
- `cargo check`, doc tests, formatting, and `git diff --check` pass;
- no `load_*`, `byte_offset(...)`, or raw struct-cell range remains in the five
  struct-heavy flagship sidecars.

This is not yet a completion claim. The complete serial library run still
reaches very slow proof regressions, and a bounded full audit has not completed
after the recent Surface Click changes.

## Prioritized remaining work

### P0. Make the baseline and audit session start reliably

This blocks every later sweep.

1. Profile why initializing the first input-cursor audit session exceeds one
   minute. Compare ordinary project verification, location verification, and
   retained-session initialization so the cost is attributed to a specific
   component.
2. Fix the responsible verifier/session path. Do not merely raise the default
   timeout.
3. Run the full library and binary tests under a generous outer watchdog.
   Investigate any test that takes tens of seconds, especially certificate
   replay tests; do not leave unbounded test processes behind.

Known current frontier:

```text
click-audit --max-sites 1 examples
  inventories 249 sites
  times out initializing input-cursor at input_cursor.click:8:9 with a 1m session limit
```

### P1. Eliminate slow simple tactics

Run the profiler project by project with a large enough project watchdog to
produce an actionable frontier. Fix every completed `SIMPLE` row over 500 ms,
then reprofile before moving on.

The latest measured slow-simple frontier is owned-split-buffer:

```text
3.175s  owned_split_buffer.click:347:5  step  statement 6
1.794s  owned_split_buffer.click:257:5  step  statement 4
1.792s  owned_split_buffer.click:295:5  step  statement 5
```

These measurements remain leads, not permanent facts. Reproduce one before
changing code. Prefer a general verifier fix supported by a focused regression.

### P2. Expand remaining slow smart tactics

Once a project reports no slow simple step:

1. choose one `SMART` row over 2 seconds;
2. expand exactly its reported source location;
3. apply the emitted sidecar;
4. reprofile and normally verify the changed unit;
5. commit the successful rewrite before selecting the next row.

The latest known smart lead is:

```text
2.787s  examples/owned-vector/vector.click:387:5
        vector_push_first.contract  execute_step  statement 6
```

Do not retain older line-number lists after source rewrites. The profiler is
the authority for the next location.

### P3. Run the full generated audit

After profiling no longer exposes slow simple replay or unexpanded smart
frontiers, run:

```sh
cargo run --quiet --bin click-audit -- examples
```

For each failure:

- fix a concrete correctness bug immediately when the correct design is clear;
- treat a timeout as a performance bug and profile the timed-out component;
- stop for discussion before changing certificate semantics or another design
  boundary;
- resume from the exact `--start-at` cursor printed by the audit.

The audit must finish all currently inventoried sites. Historical retained-
session pass counts are not substitutes for a fresh full run.

### P4. Seal and verify the one-gateway invariant

After the corpus audit is green, make one bounded code audit of smart-success
paths:

- every smart tactic commits through `TacticCertificate` replay;
- no alternate expansion planner or direct smart-state commit remains;
- adding a new smart proof surface requires adding it to audit inventory;
- no theorem or certificate consumer depends on hidden ambient premises.

Remove or privatize a bypass only when a concrete bypass is found. Do not keep
this as an open-ended refactor.

## Completion criteria

This effort is done when all of the following are true:

- full library, binary, and example tests pass under explicit outer watchdogs;
- `click-profile examples` completes project by project with no `SIMPLE` row
  over 500 ms, no `SMART` row over 2 seconds, and no unexplained timeout;
- `click-audit examples` completes every inventoried site;
- every audited rewrite reparses, reverifies, changes only its selected proof
  unit, and is idempotent;
- the bounded smart-success code audit finds no certificate bypass;
- child-process cleanup is confirmed after profiler, expander, verifier, and
  audit timeouts.

## Deferred, not blockers

Do not hold completion for these unless current work proves one is necessary:

- emitting a patch instead of the complete rewritten sidecar;
- caching standalone `click-expand` prefix replay;
- reducing duplicate rows at very low profiler thresholds;
- changing the profiler's suggested expansion timeout;
- general proof-size optimization below the 2-second smart threshold.

## Working rules

- Fix correctness bugs before continuing a sweep.
- No generic fallbacks, hidden ambient assumptions, or internal-only
  certificate tactics.
- Reproduce stale timing claims before acting on them.
- Change one frontier at a time and commit each independently verified fix.
- Use bounded commands and confirm timed-out children are reaped.
