# `int32_range` refuses a bound tighter than the `int32` range

`int32_range` states one term's own `int32` range, `n <= 2147483647`, which
holds of every `n`. `n <= 2147483646` is false at `n == 2147483647`, so the
kernel refuses it as an `int32_range` step; accepted, it would let `i <= n`
bound `i` by `2147483645` and prove the false `0 <= i + 1` over
`i == n == 2147483647` once `i < n` is weakened to `i <= n`. The true step is
in `mdtests/arithmetic_bounds_a_strict_lower_side_below_int32_max.md`.

```c filename=arithmetic_int32_range_refuses_a_bound_tighter_than_the_range.c
int32 next_index(int32 i, int32 n) {
    return 0;
}
```

```click
verifying "arithmetic_int32_range_refuses_a_bound_tighter_than_the_range.c";

theorem successor_nonnegative(i: int32, n: int32) {
    requires 0 <= i;
    requires i <= n;
    ensures 0 <= i + 1 by {
        arithmetic_certificate signed_int32 {
            premise 0: 0 <= i => 0 <= i;
            premise 1: i <= n => i <= n;
            int32_range => n <= 2147483646;
            add 1, 2 => (i + n) <= (n + 2147483646);
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
    ensures result == 0 by auto;
}
```

```expect
fail: NodeResultMismatch(2)
```
