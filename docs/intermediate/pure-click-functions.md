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

## Well-Founded Recursion

A pure function may recurse when it declares an integer measure:

```click
function countdown(n: int32) -> int32
    decreases n
{
    if n <= 0 { 0 } else { countdown(n - 1) }
}
```

Unlike a C contract, a pure function denotes a value and must be total. Click
therefore checks every call inside a direct or mutual recursive component. On
each reachable recursive edge, the callee measure must be nonnegative and
strictly smaller than the caller measure. A path that makes no recursive call
does not need a nonnegative incoming measure, so the example returns `0` for a
negative argument without recursing.

The first recursion slice deliberately keeps the proof rule easy to audit:
`decreases` names one `int32` parameter, recursive components use only `int32`
parameters and results, and a decreasing call is written as that parameter
minus a positive constant (or as a smaller nonnegative constant) under an
explicit comparison guard. Lexicographic measures and recursive array
summaries are not yet supported.

Concrete arguments unfold until evaluation reaches a base case. At symbolic
arguments, Click exposes one defining equation and preserves the next
unknown-depth call as an opaque pure-function application. The same application
is structurally equal to itself, but Click does not recursively normalize it by
an arbitrary depth budget. General induction over the measure remains separate
proof functionality.

## When To Use Pure Functions

Use a pure Click function when:

- a property depends on a computed summary,
- a predicate would otherwise duplicate logic,
- or a standard library concept should be written in Click rather than
  hard-coded into the kernel.

If a function becomes hard to prove, the missing piece might be a general proof
rule, a better predicate abstraction, or a simpler library definition.
