# Bound every Surface Click reconstruction search

## Problem

Surface reconstruction is part of Click's trusted proof-tool boundary: smart
proofs, `click expand`, and `click audit` must turn kernel facts into finite,
parseable Surface Click. A reconstruction candidate can recursively request
another spelling. The owned-vector work exposed one cycle in which a load was
spelled as `local[index]`, the derived index contained another load, and each
recursive attempt constructed a larger index. The process exhausted its stack
before the ordinary verification deadline could report a failure.

The exact local-index cycle is fixed, but that local rejection is not a general
totality guarantee. A new pointer, term, proposition, resource, or program-point
candidate could create another increasing recursion that never revisits an
identical node.

## Invariant

Untrusted proof shape and failed Surface Click synthesis must never abort the
verifier process. Every reconstruction attempt must either produce a checked
surface expression within a finite work bound or return a compact error naming
the proof site and reconstruction category.

A wall-clock deadline alone is insufficient: recursive code can consume the
native stack before reaching another deadline checkpoint.

## Design

- Give one reconstruction attempt an explicit node/work budget shared by
  proposition, condition, bitvector, pointer, offset, resource, and
  program-point synthesis.
- Prefer iterative traversal where practical. Where recursion remains, enforce
  a conservative structural depth limit before descending.
- Track the candidate class being attempted, such as parameter-relative
  pointer, local-relative indexed load, field load, or snapshot variant.
- Treat budget exhaustion as candidate failure during search. If no candidate
  works, report one bounded diagnostic with the claim, source location, and the
  most relevant exhausted category; do not dump the kernel term or state.
- Keep the existing semantic checks. A budget may reject an inexpressible or
  pathologically large spelling, but it must not make an unchecked spelling
  acceptable.

## Regression

Add a focused reconstruction test based on the former growing-local-index
cycle: the requested load and a local pointer share a symbolic block, but the
derived relative index contains a further load. The test must finish normally
and reject that candidate without requiring a larger thread stack.

Also retain direct native verification of `examples/binary-tree`, especially
`tree_rotate_left`, because its nested loaded pointers exposed the original
process abort. Include a deliberately deep but finite surface term to establish
the documented boundary behavior.

## Acceptance criteria

- No Surface Click reconstruction path can recurse without consuming an
  explicit structural or work budget.
- The growing-local-index regression returns normally with a bounded result.
- A too-deep finite term produces a concise diagnostic containing the claim and
  source site, not a stack overflow or internal-state dump.
- Binary-tree verification, owned-vector expansion, and their audit sites still
  pass with the native Click CLI.
- No wrapper process, larger stack, raised verification timeout, or quarantine
  is used to contain the problem.
