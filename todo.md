# List Prelude Roadmap

Candidate future list functions for the prelude. The rough goal is a
Lisp/Haskell-style standard library, while keeping proof obligations close to
the current `append`/`reverse` complexity.

## Needs Predicate Or Index Design

These are mostly unblocked, but still need the exact theorem surface chosen.

1. `elem-index` - return `some` first matching index or `none`.
2. `partition` - split a list into elements that pass/fail a predicate.

## Needs Nat/List Algebra

This should build on the existing natural-number/list arithmetic facts.

3. `split-at` - pair of `take n list` and `drop n list`.
