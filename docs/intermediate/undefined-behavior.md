# Undefined Behavior

Click proves more than postconditions. It also checks that the modeled C0
execution is safe under the function's requirements.

For beginner scalar code, signed overflow is the first place this appears.

```c
int32 increment(int32 x) {
    return x + 1;
}
```

This contract is incomplete:

```click
int32 increment(int32 x) {
    ensures result == x + 1 by auto;
}
```

If `x` is `2147483647`, then `x + 1` overflows signed `int32`, which is C
undefined behavior. The proof needs:

```click
requires x < 2147483647;
```

## Common UB Obligations

Click currently models obligations for cases such as:

- signed `int32` overflow,
- division or remainder by zero,
- `INT_MIN / -1` and `INT_MIN % -1`,
- invalid shift counts,
- invalid signed left shifts,
- out-of-bounds memory access.

The C0 subset reference has the full current list.

## Requirements Are Safety Facts

A requirement can be needed even when the mathematical postcondition looks
obvious:

```click
requires y != 0;
ensures result == x / y by auto;
```

The requirement is not just saying "assume division is meaningful." It rules out
a bad C execution.

## Debugging UB Failures

When a proof fails because of undefined behavior, look for the operation that
needs a safety fact:

- arithmetic needs numeric bounds,
- division needs nonzero divisors,
- shifts need valid counts and representable results,
- memory access needs valid ranges and index bounds.

The right fix is usually a requirement, a loop invariant, or a narrower
contract. Do not hide the obligation in the postcondition; Click needs the fact
before the C operation executes.
