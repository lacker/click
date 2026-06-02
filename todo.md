# List Prelude Roadmap

Candidate list functions for the prelude. The rough goal is a Lisp/Haskell-style
standard library, while keeping proof obligations close to the current
`append`/`reverse` complexity.

## Available Now

These use only plain finite lists and existing computation/effect machinery.

1. `append` - concatenate two lists. Done.
2. `reverse` - reverse a list. Done.
3. `concat` - flatten a list of lists with `append`.
4. `snoc` - append one value to the end of a list.
5. `last` - return the final element, with an error on `nil`.
6. `init` - return all but the final element, with an error on `nil`.
7. `is-singleton` - decide whether a list has exactly one element. Needs booleans.

## Needs Equality Or Booleans

These become much cleaner after we define a boolean convention and value equality
predicate/function.

8. `null` - true iff the list is `nil`.
9. `member` - true iff a value appears in a list.
10. `elem-index` - return the first matching index. Also needs naturals/options.
11. `find` - return the first element satisfying a predicate. Needs predicates/options.
12. `any` - true iff a predicate holds for some element.
13. `all` - true iff a predicate holds for every element.
14. `filter` - keep elements satisfying a predicate.
15. `partition` - split a list into elements that pass/fail a predicate.

## Needs Naturals

These need a natural-number representation and basic arithmetic theorems.

16. `length` - count list elements.
17. `nth` - return the element at an index, with an error or option on out-of-bounds.
18. `take` - first `n` elements.
19. `drop` - remove first `n` elements.
20. `split-at` - pair of `take n list` and `drop n list`.
21. `replicate` - build a list with `n` copies of a value.
22. `range` - build a list of natural numbers.

## Higher-Order List Functions

These need a clear convention for applying function values and propagating
errors/divergence.

23. `map` - apply a function to each element.
24. `fold-left` - strict accumulator fold from the left.
25. `fold-right` - fold from the right.
26. `concat-map` - map each element to a list, then concatenate.
27. `zip-with` - combine two lists elementwise with a function.

## Pair/List Shape Utilities

These use Lisp-style pairs encoded as two-element lists or cons cells. We should
pick the representation before adding them.

28. `zip` - combine two lists into a list of pairs.
29. `unzip` - split a list of pairs into a pair of lists.
30. `intersperse` - place a separator between list elements.
31. `intercalate` - concatenate a list of lists with a separator list.

## Likely First Batch

The next low-friction additions are:

1. `concat`
2. `snoc`
3. `last`
4. `init`

After that, define booleans and naturals before adding `length`, `map`,
`filter`, `take`, and `drop`.
