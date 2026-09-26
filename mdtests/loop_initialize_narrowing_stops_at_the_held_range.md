# Narrowing under a universal in `initialize` stops at the held range

The negative of
[`loop_initialize_narrows_a_held_range_under_a_universal.md`](loop_initialize_narrows_a_held_range_under_a_universal.md).
The invariant claims one prefix too many: at `k == n + 1` the range
`a[0..n + 1]` reaches past the held `views a[0..n]`, so nothing in scope makes
it viewable. The same `initialize` proof must refuse it rather than narrow the
held range past its end.

```c filename=loop_initialize_narrowing_stops_at_the_held_range.c
int32 count_up(int32 *a, int32 n) {
    int32 steps = 0;
    for (int32 i = 0; i < n; i++) {
        steps = i;
    }
    return steps;
}
```

```click
verifying "loop_initialize_narrowing_stops_at_the_held_range.c";

int32 count_up(int32 *a, int32 n) {
    views a[0..n];
    requires 0 <= n;
    requires n <= 1073741823;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        invariant forall (k: int32) { 0 <= k and k <= n + 1 implies viewable(a[0..k]) };
        initialize by {
            have forall (k: int32) { 0 <= k and k <= n + 1 implies viewable(a[0..k]) } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k <= n + 1);
                simp();
            }
            simp();
        }
    }
    execute();
    simp();
}
```

```expect
fail: `viewable(a[0..k])` was not proved
```
