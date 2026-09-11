# A representable final sum does not excuse an overflowing prefix

The final mathematical sum is `INT32_MAX`, but the second loop addition is
`INT32_MAX + 1`.  This neighboring concrete case protects the proof boundary
against checking only the result after the loop.

```c filename=integer_sum_range_fold_intermediate_overflow.c
int32 sum_prefix_overflow() {
    int32 a[3];
    int32 total;
    int32 i;
    a[0] = 2147483647;
    a[1] = 1;
    a[2] = -1;
    total = 0;
    i = 0;
    while (i < 3) {
        total = total + a[i];
        i = i + 1;
    }
    return total;
}
```

```click
verifying "integer_sum_range_fold_intermediate_overflow.c";

int32 sum_prefix_overflow() {
    ensures result == 2147483647;
} by {
    execute();
    simp();
}
```

```expect
fail: undefined behavior: signed overflow
```
