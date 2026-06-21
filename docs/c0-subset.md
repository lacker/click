# C0 Subset

C0 is this repository's small C subset. It is not a standard language. The
subset exists so proof features can be developed against a precise target before
Click grows toward real C.

## Supported Types

- `int32`
- `int32*`
- Function parameters written as `int32 p[]` or `int32 p[3]`, lowered like C
  array parameters to `int32*`.
- Local fixed-size arrays such as `int32 a[3];`.

Pointers are semantic objects with provenance blocks and pointer-offset terms.
They are not modeled as `int32` values. The current target layout assumes
8-byte pointer objects.

## Supported Expressions And Statements

Supported C0 surface includes:

- integer literals and variables
- signed `+` and `-`
- signed comparisons and equality
- assignment and sequencing
- `if` / `else` using C scalar truthiness
- `while`
- `return`
- address-of lvalues
- pointer arithmetic for `int32*`
- pointer loads and stores
- `p[i]` indexing for `int32*`
- known function calls through the current function environment
- local `int32`, `int32*`, and fixed-size `int32[N]` declarations

Comparisons return C-style `int32` values: `0` or `1`. They are not Click
propositions by themselves.

## Undefined Behavior

Signed overflow is C undefined behavior. Proofs involving signed arithmetic
usually need requirements such as:

```click
requires x < 2147483647;
requires x > -2147483648;
```

Out-of-bounds memory accesses become proof obligations or undefined behavior
depending on the symbolic execution path. Prove access safety with
`valid_range(...)`, index bounds, and loop invariants.

## Local Arrays

Local arrays allocate stack memory blocks:

```c
int32 local_array_roundtrip() {
    int32 a[3];
    a[0] = 7;
    return a[0];
}
```

An array name decays to an `int32*` rvalue for indexing and function arguments.
Direct assignment to an array object is rejected.

## Loops

`while` loops can be handled in two ways:

- bounded execution for small concrete loops
- loop verification conditions using `loop N { invariant ... }` annotations

Symbolic pointer-writing loops should use invariants and explicit loop effects.
Do not expect unconstrained symbolic loops to be unrolled automatically.

## Unsupported Or Easy-To-Forget C

These are not general C features yet:

- structs, unions, enums
- unsigned integers
- integer widths other than `int32`
- multiplication in ordinary C expressions
- casts and promotions
- pointer comparisons beyond the supported equality/range patterns
- heap allocation
- function pointers
- global variables
- `for`, `do while`, `switch`, `break`, `continue`
- compound assignments, increments, decrements
- arbitrary expressions in declarations

If you need one of these, add the smallest mdtest that motivates it before
expanding the parser or kernel.
