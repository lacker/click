# Make direct CLI deadlines interrupt derivation search

## Problem

A direct bounded verification can remain inside an explicit `derive using`
proof well past both the simple-tactic budget and the project time limit. The
owned-vector growth proof exposed this with:

```sh
target/debug/click verify --time-limit 10s examples/owned-vector/vector.click
```

The process was still running after one minute and had to be killed. This is a
tooling bug, not an example-proof problem: `click verify --time-limit` must be
a complete in-process bound and users must not need an external timeout
wrapper.

## Intended regression

Reduce the triggering post-execution `derive using` proof to a focused test
whose proposition search is deliberately large enough to cross a tiny test
deadline. Exercise it through the same derivation planner used by Click proof
replay, not by sleeping or by wrapping the CLI process.

The checked path must poll the active deadline while exploring derivations and
return Click's ordinary bounded diagnostic. The diagnostic must identify the
active tactic without dumping the search state.

## Acceptance criteria

- General proposition-derivation search cooperatively checks the active tactic
  and project deadlines.
- `click verify --time-limit` returns on the bounded path without a wrapper or
  orphaned verifier process.
- The focused regression deterministically exercises cancellation without
  relying on wall-clock scheduling.
- Ordinary derivation, mdtest, and example suites remain green and within
  their tactic budgets.
