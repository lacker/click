# Current Limitations

This page lists boundaries that agents should not silently assume away.

## C0 Is Small

Click does not parse general C. See [c0-subset.md](c0-subset.md). Missing
features include structs, unsigned integers, casts, globals, heap allocation,
`for` loops, `switch`, and many operators.

## Aliasing Is Default

Distinct pointer parameters may alias. Add `disjoint(...)` whenever a proof
depends on non-overlap.

## Requirements Cannot Freely Read Memory

Direct memory reads in `requires` propositions are limited. Use a named
predicate for memory-reading preconditions, and unfold it in proof scripts when
the body is needed.

## Predicates Are Opaque

Predicate calls are not unfolded automatically. Exact predicate facts can be
reused, but proving a predicate body or using its consequences generally needs:

```click
unfold(predicate_name);
```

## `old(...)` Has One Entry State

`old(...)` evaluates in the function-entry memory. Predicates themselves carry
one implicit memory argument. A predicate like `permutation(a, b, lo, hi)`
compares two arrays in the same memory state; it does not automatically compare
current `a` to old `a`.

## Symbolic `.any` Is Not General Yet

`(lo..hi).any(...)` currently requires concrete bounds and unrolls to a finite
disjunction. There is no general existential proposition surface yet.

## Folds Are Partly Supported

Pure `.fold` supports concrete unrolling and symbolic `RangeFold` terms. The
kernel knows useful fold facts for current stdlib `count` proofs, but it is not
a general induction engine for arbitrary folds.

## Loop Invariants Need Explicit Facts

Pointer-writing loops do not implicitly preserve memory. Use invariants,
`mutable` effects, and `disjoint` requirements. Symbolic loops need invariants
for arithmetic bounds, memory safety, and postconditions.

## `simp` Is Not A Solver

`simp` performs deterministic local normalization and selected proof rules. It
does not search broadly, infer missing invariants, synthesize frame conditions,
or invent arithmetic lemmas.

## Diagnostics Are Developer-Oriented

Failure messages expose internal propositions, path facts, and memory terms.
They are useful for agents but not yet polished for end users.
