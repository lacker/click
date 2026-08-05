# Align branched expansion certificates by execution path

## Problem

Selecting a smart arithmetic tactic inside the owned-vector growth proof made
`click-expand` fail elsewhere with:

```text
surface proof has 1 leaves but frame certificate has 2 paths
```

The proof contained a searched `execute()` followed by an `if result == 0`
proof. Expansion associated a one-leaf surface proof with a two-path frame
certificate instead of aligning certificate material with the corresponding
execution branch.

This is independent of whether the selected arithmetic tactic is expandable.
Expanding one site must not corrupt or reinterpret a sibling control-flow
certificate.

## Intended design

- Give proof paths stable identities derived from checked branch structure,
  rather than relying on vector position or leaf count.
- Associate frame and execution certificates with those identities.
- Require exact path coverage when rewriting a proof container and diagnose the
  first missing or duplicate path compactly.
- Preserve unselected tactic text and certificate semantics byte-for-byte or by
  a checked structural equivalent.

## Regression

Add a small two-result C function and a Click proof with `execute(); if result
== 0 { ... } else { ... }`. Put an expandable smart `have` in one branch and a
different frame shape in the other. Expanding either branch must produce a
parseable file, verify, and reach an expansion fixed point.

## Acceptance criteria

- Expansion works when searched execution and surface control flow have
  multiple paths.
- Selecting one tactic cannot fail because of an unselected sibling's leaf
  count.
- Missing path alignment is detected before output and names compact path IDs.
- The regression runs through `click-expand`, targeted verification, and the
  audit fixed-point check.
