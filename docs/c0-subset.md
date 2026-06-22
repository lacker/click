# C0 Subset

C0 is this repository's small C subset. It is not a standard language. The
subset exists so proof features can be developed against a precise target before
Click grows toward real C.

## Supported Types

- `int32`
- `uint8`
- `int32*`
- `uint8*`
- Function parameters written as `int32 p[]`, `int32 p[3]`, `uint8 p[]`, or
  `uint8 p[3]`, lowered like C array parameters to pointers.
- Local fixed-size arrays such as `int32 a[3];` and `uint8 bytes[16];`.

Pointers are semantic objects with provenance blocks and pointer-offset terms.
They are not modeled as `int32` values. The current target layout assumes
8-byte pointer objects.

## Supported Expressions And Statements

Supported C0 surface includes:

- integer literals and variables
- ASCII byte character literals such as `'x'`, `'\n'`, and `'\0'`
- signed `+` and `-`
- signed comparisons and equality
- assignment and sequencing
- `if` / `else` using C scalar truthiness
- `while`
- `return`
- address-of lvalues
- pointer arithmetic for `int32*` and `uint8*`, scaled by the pointee width
- pointer loads and stores
- `p[i]` indexing for `int32*` and `uint8*`
- known function calls through the current function environment
- local scalar, pointer, and fixed-size array declarations for `int32` and
  `uint8`

Comparisons return C-style `int32` values: `0` or `1`. They are not Click
propositions by themselves. Ordered comparisons are currently for `int32`;
`uint8` supports equality, inequality, truthiness, loads, stores, and returns.

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
uint8 local_byte_array() {
    uint8 a[2];
    a[0] = 'x';
    a[1] = 'y';
    return a[0];
}
```

An array name decays to a pointer rvalue for indexing and function arguments.
Direct assignment to an array object is rejected. `int32` arrays allocate four
bytes per element; `uint8` arrays allocate one byte per element.

## Loops

`while` loops can be handled in two ways:

- bounded execution for small concrete loops
- loop verification conditions using `loop N { invariant ... }` annotations

Symbolic pointer-writing loops should use invariants and explicit loop effects.
Do not expect unconstrained symbolic loops to be unrolled automatically.

## Unsupported Or Easy-To-Forget C

These are not general C features yet:

- structs, unions, enums
- unsigned integers other than the narrow `uint8` byte type
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
