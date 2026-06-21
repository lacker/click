# Standard Library

The standard library currently lives in:

```text
stdlib/prelude.click
```

It is parsed as ordinary Click source by `src/lang/click.rs`. Standard-library
definitions are not hard-coded predicates or functions in the Click parser.

## Current Prelude

```click
function count(int32 p[], int32 lo, int32 hi, int32 x) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}

predicate permutation(int32 a[], int32 b[], int32 lo, int32 hi) {
    forall (int32 x) {
        count(a, lo, hi, x) == count(b, lo, hi, x)
    }
}
```

`count` is a pure Click function over a range. `permutation` is a Click
predicate saying every `int32` value has the same count in both arrays over the
same half-open range. The array parameters are Click array refs, so callers can
write `permutation(p, old(p), lo, hi)` to compare current memory with
entry-state memory.

## Kernel Support

The names `count` and `permutation` are library names, not kernel concepts.
However, the kernel has general term/proof support that makes these definitions
usable:

- `Bitvector32Term::RangeFold` represents symbolic folds.
- Empty folds simplify to the initial value.
- One-step folds substitute the item and accumulator once.
- Small concrete folds unroll.
- Count-shaped folds can be matched across a split range.
- Count sums are compared modulo addend order.

This is the intended pattern: keep definitions in Click where possible, and add
general proof support to the kernel only when the proof engine needs it.

## Namespace Behavior

Stdlib definitions are combined with user Click definitions during validation.
A user Click function or predicate cannot redefine a stdlib name. A C function
spec may still have the same name as a stdlib Click function when there is no
user Click definition conflict.

## Current Example

`mdtests/compare_swap2_permutation.md` proves that a two-cell compare-swap
preserves `permutation(p, old(p), 0, 2)` without copying the original values
into a separate snapshot array.

## Adding A Library Function

1. Add the definition to `stdlib/prelude.click`.
2. Add an mdtest using it from an ordinary `.click` sidecar.
3. If the proof does not close, decide whether the missing support is:
   - a general kernel/prover law
   - a missing proof step
   - a language feature
   - a bad library abstraction
4. Update this document.

Avoid putting domain-specific definitions directly in the kernel just because
they are useful. Prefer stdlib definitions backed by general proof support.
