# Integer arithmetic preserves selectors on comparison operands

Combining a bound at iteration entry with a current equality must retain the
original operand states in its printable, checked certificate.

```c filename=integer_state_arithmetic.c
void transfer(int32 progress, int32 total, int32 end) {
    progress = progress - 1;
}
```

```click
verifying "integer_state_arithmetic.c";
void transfer(int32 progress, int32 total, int32 end) {
    requires 0 < progress;
    requires to_integer(total) <= 255 * to_integer(progress);
    requires to_integer(end) == to_integer(progress);
    ensures to_integer(total) <= 255 * to_integer(end);
} by {
    step();
    have to_integer(end) == at(region(0).entry, to_integer(progress));
    have to_integer(total) <= 255 * to_integer(end) by {
        solve() using {
            at(region(0).entry, to_integer(total) <= 255 * to_integer(progress));
            to_integer(end) == at(region(0).entry, to_integer(progress));
        };
    }
}
```

```expect
pass
```
