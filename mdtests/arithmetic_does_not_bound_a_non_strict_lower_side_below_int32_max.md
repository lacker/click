# `arithmetic()` does not bound the lower side of a non-strict premise below `INT32_MAX`

`i <= n` allows `i == n == 2147483647`, where `i + 1` overflows, so
`0 <= i; i <= n` does not show `0 <= i + 1`. The int32 range of `n` bounds
`i` only by `2147483647`, and the planner refuses rather than print a
certificate the kernel would reject. The strict neighbour is
`mdtests/arithmetic_bounds_a_strict_lower_side_below_int32_max.md`.

```c filename=arithmetic_does_not_bound_a_non_strict_lower_side_below_int32_max.c
int32 next_index(int32 i, int32 n) {
    return 0;
}
```

```click
verifying "arithmetic_does_not_bound_a_non_strict_lower_side_below_int32_max.c";

theorem successor_nonnegative(i: int32, n: int32) {
    requires 0 <= i;
    requires i <= n;
    ensures 0 <= i + 1 by {
        arithmetic() using { 0 <= i; i <= n; }
    }
}

int32 next_index(int32 i, int32 n) {
    ensures result == 0 by auto;
}
```

```expect
fail: `arithmetic` cannot establish that every int32 operation in the current goal is defined without overflow from exactly the listed premises
```
