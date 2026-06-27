# C0 Subset

C0 is this repository's small C subset. It is not a standard language. The
subset exists so proof features can be developed against a precise target before
Click grows toward real C. When C0 syntax appears inside Surface Click, this
documentation calls that syntax a **C fragment**.

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
- signed `+`, `-`, `*`, `/`, and `%`
- `int32` shifts `<<` and `>>`
- `int32` bitwise `&`, `|`, `^`, and unary `~` with fixed 32-bit
  two's-complement bitvector semantics
- signed comparisons and equality
- assignment and sequencing
- statement update sugar: `x++`, `x--`, `x += expr`, `x -= expr`, and
  `x *= expr`
- `if` / `else` using C scalar truthiness
- `while`
- assignment-style `for (init; condition; step)` loops lowered to `while`
- `return`
- address-of lvalues
- pointer arithmetic for `int32*` and `uint8*`, scaled by the pointee width
- pointer loads and stores
- `p[i]` indexing for `int32*` and `uint8*`
- known function calls through the current function environment
- local scalar, pointer, and fixed-size array declarations for `int32` and
  `uint8`

Comparisons return C-style `int32` values: `0` or `1`. They are not Click
propositions by themselves. Ordered comparisons, shifts, and bitwise operators
are currently for `int32`; `uint8` supports equality, inequality, truthiness,
loads, stores, and returns.

C0 follows the GCC/Clang/MSVC consensus for signed right shift: `int32 >> k`
is arithmetic right shift with sign extension. This is implementation-defined
in ISO C for negative signed values, but it is the behavior of the mainstream
compilers Click is targeting.

## Undefined Behavior

Signed overflow is C undefined behavior. Signed division and remainder also
have C undefined behavior for a zero divisor, and for `INT_MIN / -1` or
`INT_MIN % -1`. Shift counts must be in `0..32`. Signed left shift is undefined
for a negative left operand or an unrepresentable `int32` result. Proofs
involving signed arithmetic usually need requirements such as:

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

The first `for` slice is sugar for existing `while` semantics:
`for (i = init; condition; step) { body }` lowers to `i = init; while
(condition) { body; step; }`. The initializer must be a scalar assignment. The
step may be a scalar assignment or one of the supported scalar update-statement
forms. Declarations inside the `for` initializer, omitted clauses, and
`continue` are not supported yet.

Symbolic pointer-writing loops should use invariants and explicit loop effects.
Do not expect unconstrained symbolic loops to be unrolled automatically.

## Unsupported Or Easy-To-Forget C

These are not general C features yet:

- structs, unions, enums
- unsigned integers other than the narrow `uint8` byte type
- integer widths other than `int32`
- casts and promotions
- shifts and bitwise operators on `uint8` or promoted/mixed-width integer
  expressions
- pointer comparisons beyond the supported equality/range patterns
- heap allocation
- function pointers
- global variables
- `do while`, `switch`, `break`, `continue`
- declarations or omitted clauses inside `for` loops
- update expressions inside larger expressions, such as `j = i++`
- compound/update operations on non-scalar lvalues, such as `p[i]++`
- arbitrary expressions in declarations

If you need one of these, add the smallest mdtest that motivates it before
expanding the parser or kernel.
