# A viewable-range invariant owes its symbolic extent at entry

The loop head assumes a stated range's extent half as invariant content, so
the entry owes it as a judgment of its own, beside the declaration's body.
Here `k` starts at `s`, which nothing bounds below, so `0 <= k` is not
established at entry and the loop is refused there, naming that condition.
The entry used to owe only the body under the extent as a guard, which would
have let the head assume `0 <= k` for the false `ensures result >= 0`.

The body keeps `k` loop-modified so the head reads it as an unknown value; the
C is synthetic.

```c filename=loop_invariant_viewable_range_extent_is_owed_at_entry.c
int32 walk(int32 *a, int32 n, int32 s) {
    int32 k;
    int32 i;
    k = s;
    i = 0;
    while (i < n) {
        i = i + 1;
        k = k * 1;
    }
    return k;
}
```

```click
verifying "loop_invariant_viewable_range_extent_is_owed_at_entry.c";

int32 walk(int32 *a, int32 n, int32 s) {
    views a[0..n];
    requires s <= n;
    requires n <= 1073741823;
    requires 0 <= n;
    ensures result >= 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        invariant viewable(a[0..k]);
    }
    step();
    simp();
}
```

```expect
fail: loop 0 invariant 2 entry, owing `0 <= k`
```
