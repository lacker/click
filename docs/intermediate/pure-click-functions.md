# Pure Click Functions

Pure Click functions compute specification values. They do not run as C code.

For example, the standard library defines `count`:

```click
function count(p: int32[], lo: int32, hi: int32, x: int32) -> int32 {
    (lo..hi).fold(0, |acc, k| {
        acc + if p[k] == x { 1 } else { 0 }
    })
}
```

This function counts occurrences in a range of an array-ref parameter.

Pure Click functions can use immutable `let` bindings:

```click
function inc_with_let(x: int32) -> int32 {
    let next: int32 = x + 1;
    next
}
```

The annotation is optional when the value's type is already clear:

```click
let next = x + 1;
```

## Functions Versus Predicates

A pure Click function returns a value:

```click
function count(...) -> int32 { ... }
```

A predicate returns a proposition:

```click
predicate permutation(a: int32[], b: int32[], lo: int32, hi: int32) {
    forall (x: int32) {
        count(a, lo, hi, x) == count(b, lo, hi, x)
    }
}
```

Use functions for reusable computed values. Use predicates for reusable facts.

## Array Refs

When a pure Click function takes `int32 p[]` or `uint8 p[]`, the parameter is a
specification-level array ref. It contains:

- a memory snapshot,
- a pointer,
- and an element type.

That is why this postcondition works:

```click
ensures permutation(p, old(p), 0, n) by auto;
```

The first `p` means the current array. `old(p)` means the function-entry array
at the same pointer.

## Folds

Range folds express computations over ranges:

```click
(lo..hi).fold(init, |acc, k| {
    ...
})
```

The kernel has selected reasoning support for the current standard-library
folds, especially `count` and `permutation`. It is not yet a general induction
engine for arbitrary folds.

## When To Use Pure Functions

Use a pure Click function when:

- a property depends on a computed summary,
- a predicate would otherwise duplicate logic,
- or a standard library concept should be written in Click rather than
  hard-coded into the kernel.

If a function becomes hard to prove, the missing piece might be a general proof
rule, a better predicate abstraction, or a simpler library definition.
