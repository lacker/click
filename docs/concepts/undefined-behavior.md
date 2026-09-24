# Undefined behavior

Click proves more than postconditions. It also checks that the modeled C0
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

- signed `int32` overflow,
- division or remainder by zero,
- `INT_MIN / -1` and `INT_MIN % -1`,
- invalid shift counts,
- invalid signed left shifts,
- out-of-bounds memory access,
- reads of uninitialized automatic storage,
- loads, stores, and pointer operations through a freed allocation.

The C0 subset reference has the full current list.

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
- converting it to an integer by a cast, or to `_Bool` by a cast or an
  assignment.

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
or a structure field, storing it, passing it to a call, and a
pointer-to-pointer cast all move the value without using it. A different
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
- local reads need an assignment on every path that reaches them.
- pointer comparisons, differences, truth tests, and integer conversions need
  the pointer's allocation to still be live.

The right fix is usually a requirement, a loop invariant, or a narrower
contract. Do not hide the obligation in the postcondition; Click needs the fact
before the C operation executes.
