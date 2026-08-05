# Bound and summarize verifier diagnostics

## Problem

Allocation-growth failures printed complete symbolic memories, heaps, resource
contexts, contracts, and certified paths. Individual diagnostics reached
hundreds of kilobytes. The actionable sentence was followed by enough internal
state to be truncated by the terminal/tool boundary.

This is a usability and performance bug. A diagnostic must preserve the cause
without serializing the verifier's entire state graph by default.

## Intended design

Introduce structured diagnostic rendering with explicit size budgets:

- lead with source unit, path/branch, tactic or claim, and the violated
  invariant;
- show a compact difference: missing/extra resources, mismatched outcome, or
  unverified claim keys;
- name repeated symbolic memories and terms once instead of recursively
  printing them at every occurrence;
- cap item counts and total characters with deterministic omission summaries;
- keep full debug state behind an explicit environment variable or output-file
  option intended for engine debugging.

The cap belongs in the shared verifier diagnostic layer. `click-audit` already
truncates child output, but every direct consumer, including `click-verify` and
tests, needs bounded diagnostics before the string is constructed.

## Regression

Reduce the owned-vector ghost-resource mismatch to a focused kernel or mdtest
fixture. Assert that the diagnostic includes the resource delta and claim name,
does not include a recursively expanded complete contract, and stays under the
chosen default bound. Include Unicode in one fixture so truncation remains
character-safe.

## Acceptance criteria

- Direct verifier failures have a documented maximum default size.
- Resource and execution mismatches render concise deltas.
- Full internal state is opt-in and does not contaminate normal test output.
- Tests cover size, determinism, character boundaries, and preservation of the
  primary cause.
