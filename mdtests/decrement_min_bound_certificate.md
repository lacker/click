# Decrement safety replays from the strict minimum bound

The direct precondition that an `int32` value is above `INT32_MIN` is exactly
the condition needed to certify that subtracting one does not overflow.

```c filename=decrement_min_bound_certificate.c
struct counter {
    int32 value;
};

void decrement(struct counter* counter) {
    counter->value = counter->value - 1;
}
```

```click
verifying "decrement_min_bound_certificate.c";

void decrement(struct counter* counter) {
    requires -2147483648 < counter->value;
    owns counter->value;
    mutable counter->value;
} by {
    execute();
    frame();
    simp();
}
```

```expect
pass
```
