# `arithmetic()` bounds the lower side of a strict premise below `INT32_MAX`

`i < n` with `n` an `int32` means `n <= 2147483647`, so `i <= 2147483646`
and `i + 1` cannot overflow. With `0 <= i` beside it, `0 <= i + 1` follows.
No premise bounds `n`, so the planner uses `n`'s own int32 range: the
certificate's `int32_range => n <= 2147483647` step, added to `i < n`, bounds
`i` by `2147483646`. The kernel checks that step as the range of an opaque
`int32` atom, like `interval_atom`; `successor_nonnegative_certificate` is
the certificate `click expand` prints for it, checked as written. The non-strict `i <= n` gives only
`i <= 2147483647`, which leaves `i + 1` able to overflow:
`mdtests/arithmetic_does_not_bound_a_non_strict_lower_side_below_int32_max.md`.

```c filename=arithmetic_bounds_a_strict_lower_side_below_int32_max.c
int32 next_index(int32 i, int32 n) {
    return 0;
}
```

```click
verifying "arithmetic_bounds_a_strict_lower_side_below_int32_max.c";

theorem successor_nonnegative(i: int32, n: int32) {
    requires 0 <= i;
    requires i < n;
    ensures 0 <= i + 1 by {
        arithmetic() using { 0 <= i; i < n; }
    }
}

theorem successor_nonnegative_certificate(i: int32, n: int32) {
    requires 0 <= i;
    requires i < n;
    ensures 0 <= i + 1 by {
        arithmetic_certificate signed_int32 {
            premise 0: 0 <= i => 0 <= i;
            premise 1: i < n => i < n;
            int32_range => n <= 2147483647;
            add 1, 2 => (i + n) < (n + 2147483647);
            interval_from_affine 0 (i) (0) (2147483647);
            interval_from_affine 3 (i) (-2147483648) (2147483646);
            interval_intersect 4, 5 (0) (2147483646);
            interval_atom (1) (1) (1);
            interval_add_bounded 6, 7 (1) (2147483647);
            trivial => -1 <= 0;
            add 0, 9 => (0 + -1) <= (i + 0);
            affine_conclusion 10 8 => 0 <= (i + 1);
            conclusion 11;
        }
    }
}

int32 next_index(int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    ensures result == 0;
} by {
    have 0 <= i + 1 by { arithmetic() using { 0 <= i; i < n; } }
    step();
    simp();
}
```

```expect
pass
```
