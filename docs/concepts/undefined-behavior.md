# Undefined behavior

Click proves more than postconditions. It also checks that the modeled C
execution is safe under the function's requirements.

For scalar code, signed overflow is often the first place this appears.

<!-- verified-example: mdtests/overflow.md -->
```c
int32 increment(int32 x) {
    return x + 1;
}
```

This contract is incomplete:

<!-- verified-example: mdtests/overflow.md -->
```click
int32 increment(int32 x) {
    ensures result == x + 1 by auto;
}
```

If `x` is `2147483647`, then `x + 1` overflows signed `int32`, which is C
undefined behavior. The proof needs:

<!-- verified-example: mdtests/overflow.md -->
```click
requires x < 2147483647;
```

## Common UB obligations

Click currently models obligations for cases such as:

- signed `int32` and `int64` overflow (narrower types promote to `int32`
  first),
- division or remainder by zero,
- `INT_MIN / -1` and `INT_MIN % -1`,
- invalid shift counts,
- invalid signed left shifts,
- out-of-bounds memory access,
- pointer arithmetic that leaves the pointed-to object, or an object whose
  extent is known only through the ranges the state holds,
- reads of uninitialized automatic storage,
- loads, stores, and pointer operations through a freed allocation.

The [runtime-errors table](../reference/coverage.md#runtime-errors-checked)
lists every checked error for C, C++, and Rust.

## Pointer arithmetic stays inside the object

C11 6.5.6p8 defines `p + k` only when the result points at an element of the
array object `p` points into or one past its end. For a local array or a heap
allocation Click checks the displacement against the object's size. A pointer
parameter, or any symbolic or loaded pointer, has no recorded size; the
`owns`, `views`, and `viewable` ranges the function holds for it are the only
extent Click knows, so the result must lie in one of them, its one-past end
included:

<!-- verified-example: mdtests/pointer_arithmetic_past_a_viewed_range_is_refused.md -->
```c
int32 *q = p + 1000;
```

is refused under `views p[0..4]` as `pointer arithmetic left the pointed-to
object`, while `p + 4`, `p + 0`, and `p + i` under
`requires 0 <= i and i <= 4` verify
(`mdtests/pointer_arithmetic_within_a_viewed_range_is_accepted.md`). When the
facts leave the bound open, the formation owes it as an obligation, the way a
local array's bound is owed. A pointer whose object has no held range owes
nothing at formation; the access through it is what is refused.

Equality across objects is decided from the objects alone, except for the
one configuration C leaves to object placement: a pointer one past the end of
one object compared with the start of another (C11 6.5.9p6). That comparison
is refused, naming the one-past-the-end operand, rather than answered:

<!-- verified-example: mdtests/a_one_past_the_end_pointer_is_not_compared_with_another_object.md -->
```c
int32 a[2];
int32 b[2];
return (a + 2) != b;
```

Comparing the starts of two objects, two pointers into one object, or a
pointer with null is unaffected
(`mdtests/pointers_into_distinct_objects_compare_unequal.md`). See the
memory model's [Blocks and pointers](memory-model.md#blocks-and-pointers).

## Freed pointers are indeterminate

When `free` ends an allocation's lifetime, C11 6.2.4p2 makes the value of
every pointer into that allocation indeterminate, and Annex J.2 lists using
such a value as undefined behavior. A load or store through the pointer is
refused as an invalid memory access. Operating on the pointer value itself is
refused too:

- `==` and `!=`, including a comparison with null;
- `<`, `<=`, `>`, and `>=`;
- pointer subtraction and adding or subtracting an integer offset;
- testing its truth in `if`, a loop condition, `?:`, `!`, `&&`, or `||`;
- converting it to an integer by a cast, or to `_Bool` by a cast, an
  assignment, a `return` from a `_Bool` function, or passing it as an
  argument to a `_Bool` parameter.

The diagnostic names the freed allocation, for example
`use of a pointer into freed allocation heap-allocation:1000000`.

<!-- verified-example: mdtests/freed_pointer_equality_rejected.md -->
```c
int *q = p;
free(p);
return q == p;
```

A pointer counts as freed when its own block holds an allocation base the
current snapshot has deallocated: the exact base, or an offset into it.
Copies count too, so a pointer restored through a byte-representation copy
is refused in the same way. A symbolic pointer the verifier cannot tie to a
freed block keeps its ordinary meaning.

Only operations on the value are uses. Reading the pointer out of a variable
or a structure field, storing it, passing it to a pointer parameter,
returning it from a pointer-returning function, and a pointer-to-pointer cast
all move the value without using it. A different
live pointer is unaffected, so testing it against null is still fine. The
common idioms therefore verify:

<!-- verified-example: mdtests/freed_pointer_set_to_null_verifies.md -->
```c
free(p);
p = 0;
```

<!-- verified-example: mdtests/freed_pointer_guarded_free_verifies.md -->
```c
if (p != 0) {
    free(p);
}
```

Compare pointers before the free, as
`mdtests/byte_representation_compare_before_free.md` does, when a program needs
the answer.

## Requirements are safety facts

A requirement can be needed even when the mathematical postcondition looks
obvious:

<!-- verified-example: mdtests/overflow.md -->
```click
requires y != 0;
ensures result == x / y by auto;
```

The requirement is not just saying "assume division is meaningful." It rules out
a bad C execution.

## Debugging UB failures

When a proof fails because of undefined behavior, look for the operation that
needs a safety fact:

- arithmetic needs numeric bounds,
- division needs nonzero divisors,
- shifts need valid counts and representable results,
- memory access needs viewable ranges and index bounds.
- pointer arithmetic on a parameter needs the result inside a held `owns`,
  `views`, or `viewable` range, its one-past end included.
- local reads need an assignment on every path that reaches them.
- pointer comparisons, differences, truth tests, and integer conversions need
  the pointer's allocation to still be live.

The right fix is usually a requirement, a loop invariant, or a narrower
contract. Do not hide the obligation in the postcondition; Click needs the fact
before the C operation executes.
