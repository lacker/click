# Make large expansion audits concise and scope-aware

## Problem

`click audit` is the right exhaustive check for the smart-to-simple boundary,
but its current successful workflow is expensive and noisy. Auditing the
owned-vector sidecar checked 116 sites, printed one row per site, and repeatedly
verified multi-second proof units. That is acceptable as a manual release gate,
but awkward as a normal check after a localized proof or example change.

The existing `--start-at` and `--max-sites` controls bound an investigation;
they do not determine which claims are semantically affected by a change, and
the default output makes a large all-green run difficult to scan.

## Invariant

Scoping and presentation may reduce work or output, but every selected site
must retain the current audit meaning: expand that site, replay and directly
verify the rewritten proof unit, and confirm the smart-site fixed point. A
later expansion must never mask an individually broken earlier expansion.

## Design

Implement this in stages:

1. Add a concise mode that prints inventory, claim-level progress, failures,
   resumable cursors, and the final summary. Preserve per-site rows behind a
   verbose flag.
2. Add explicit claim selection so a developer can audit one or more named
   proof units without finding line and column coordinates manually.
3. Add `--changed-since <revision>` after the dependency selection used by
   incremental verification is available. Changes to proof-engine,
   certification, kernel, parser, or printing code must conservatively select
   the full audit rather than guess at a narrow impact set.
4. Only after the serial behavior is clear, consider bounded parallelism across
   independent claims. It must use the shared audit engine directly, isolate
   mutable sessions, buffer output in deterministic source order, and stop
   cleanly on failure. Do not implement this with shell wrappers or recursively
   spawned Click commands.

Parallel execution is an optional later optimization, not a prerequisite for
the first three improvements.

## Regression

Create a small two-claim fixture with multiple smart sites in each claim. Test
that claim selection audits exactly the requested sites, concise mode reports
claim progress without successful site spam, and a failure still identifies
the exact `PATH:LINE:COLUMN` plus resume command.

For changed-since selection, test a leaf proof change, a called-contract change,
and a proof-engine source change. They should select the leaf, its dependency
closure, and the complete audit respectively.

## Acceptance criteria

- Concise output for a large passing sidecar is proportional to claims, not
  smart sites, while verbose output preserves today's detail.
- Named-claim selection is deterministic and rejects unknown or ambiguous
  names precisely.
- Changed-since selection never omits a dependent proof unit and falls back to
  the full audit for verifier-wide changes.
- Every selected site still receives individual expansion, replay, direct
  verification, and fixed-point checks.
- Interrupted runs leave no verifier workers and retain a pasteable resume
  cursor.
