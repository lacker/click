# An invariant's conversion side condition that is false at entry is refused there

The head assumes an invariant's side conditions as invariant content, here
that `i + 1` does not overflow in `to_integer(i + 1)`. That is sound only
because entry owes them. `i` starts at `s`, which may be `2147483647`, so the
side condition is not established at entry and the loop is refused there.
Were it assumed without being owed, the false `ensures defined(result + 1)`
would follow at the exit for `s == 2147483647` and `n <= s`.

```c filename=loop_invariant_conversion_side_condition_false_at_entry_is_refused.c
int32 walk(int32 s, int32 n) {
    int32 i;
    i = s;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_invariant_conversion_side_condition_false_at_entry_is_refused.c";

int32 walk(int32 s, int32 n) {
    requires 0 <= s;
    requires n < 2147483647;
    ensures defined(result + 1);
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant to_integer(i + 1) == to_integer(i + 1);
        preserve by {
            step();
            have i <= n by { simp(); }
            have i < 2147483647 by { arithmetic() using { i <= n; n < 2147483647; } }
            have defined(i + 1) by {
                apply(int32_increment_below_max_is_defined(i)) using { i < 2147483647; }
            }
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
fail: loop 0 invariant 1 entry, owing `defined((i + 1))`
```
