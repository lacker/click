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
- C logical `&&`, `||`, and unary `!` with short-circuit C scalar truthiness
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
- `free(p);` as a narrow one-cell resource operation requiring `free(p[0..1])`
- `p[i]` indexing for `int32*` and `uint8*`
- a small struct slice: `struct name { ... };`, `struct name*` pointers, and
  `p->field` loads/stores for `int32` and pointer fields
- known function calls through the current function environment
- local scalar, pointer, and fixed-size array declarations for `int32` and
  `uint8`

Comparisons return C-style `int32` values: `0` or `1`. They are not Click
propositions by themselves. `uint8` rvalues promote to `int32` for arithmetic,
ordered comparisons, shifts, and bitwise operators. Assigning or returning an
`int32` into `uint8` requires Click to prove `0 <= value <= 255`.

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
`read(...)`, `write(...)`, `valid_range(...)`, index bounds, and loop
invariants.

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

## Struct Slice

C0 supports a small struct-pointer slice:

```c
struct owner {
    int32 len;
    int32* data;
};

int32 set_first(struct owner* owner, int32 data[]) {
    int32* current;
    owner->len = 1;
    owner->data = data;
    current = owner->data;
    current[0] = owner->len;
    return current[0];
}
```

This is intentionally not a full C struct model yet. Struct fields may be
`int32` or pointer-typed fields such as `int32*`, `uint8*`, and `struct name*`.
`struct name*` is accepted for parameters and local pointers, and `p->field` is
lowered as a typed load or store at the field's compact byte offset. There is
no C ABI padding/alignment model yet, and struct values, nested struct values,
arrays of structs, and general field-address expressions are still unsupported.

Click contracts can use field places in resource clauses, such as
`read(owner->len)` and `write(owner->data)`. These lower through the same
compact field offsets, and the access resource makes the field valid for
symbolic execution. Explicit ranges such as `write(owner[0..3])` are still
available when a contract needs to describe a broader footprint. The
`valid_field(p->field)` and `mutable_field(p->field)` helpers remain as
compatibility conveniences for field-sized validity and effects.

## Loops

`while` loops can be handled in two ways:

- bounded execution for small concrete loops
- loop verification conditions using `for loop(N) { invariant ... }`
  annotations

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

- full structs, unions, enums
- unsigned integers other than the narrow `uint8` byte type
- integer widths other than `int32`
- casts beyond the current checked `int32`-to-`uint8` narrowing conversion
- mixed-width integer conversions beyond `uint8` promotion to `int32`
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
