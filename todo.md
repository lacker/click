# List Prelude Roadmap

Candidate future list functions for the prelude. The rough goal is a
Lisp/Haskell-style standard library, while keeping proof obligations close to
the current `append`/`reverse` complexity.

## Needs Equality, Predicates, Or Options

These become much cleaner after we define value equality, predicates, options, or
related helper machinery.

1. `member` - true iff a value appears in a list.
2. `elem-index` - return the first matching index. Also needs naturals/options.
3. `find` - return the first element satisfying a predicate. Needs predicates/options.
4. `partition` - split a list into elements that pass/fail a predicate.

## Needs Naturals

These need a natural-number representation and basic arithmetic theorems.

5. `length` - count list elements.
6. `nth` - return the element at an index, with an error or option on out-of-bounds.
7. `take` - first `n` elements.
8. `drop` - remove first `n` elements.
9. `split-at` - pair of `take n list` and `drop n list`.
10. `replicate` - build a list with `n` copies of a value.
11. `range` - build a list of natural numbers.

## Pair/List Shape Utilities

These use Lisp-style pairs encoded as two-element lists or cons cells. We should
pick the representation before adding them.

12. `zip` - combine two lists into a list of pairs.
13. `unzip` - split a list of pairs into a pair of lists.
14. `intersperse` - place a separator between list elements.
15. `intercalate` - concatenate a list of lists with a separator list.
