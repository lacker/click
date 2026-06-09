# List Prelude Roadmap

Candidate future list functions for the prelude. The rough goal is a
Lisp/Haskell-style standard library, while keeping proof obligations close to
the current `append`/`reverse` complexity.

## Needs Equality, Predicates, Or Options

These become much cleaner after we define predicates, options, or related helper
machinery.

1. `elem-index` - return the first matching index. Also needs naturals/options.
2. `find` - return the first element satisfying a predicate. Needs predicates/options.
3. `partition` - split a list into elements that pass/fail a predicate.

## Needs Naturals

These need a natural-number representation and basic arithmetic theorems.

4. `nth` - return the element at an index, with an error or option on out-of-bounds.
5. `split-at` - pair of `take n list` and `drop n list`.
