# A byte range's quantified viewable invariant needs no count bound

`mdtests/loop_initialize_narrows_a_held_byte_range_under_a_universal.md`
without its `requires n <= 1073741823`. A range of one-byte elements has no
count limit below `2147483647`, so that bound was never the byte range's
extent half. Dropping it was reported to make the back edge's closer refuse
the ranking member `0 <= n - i`, which follows from `0 <= i <= n` alone. The
same proof closes without it, and this file keeps it that way.

```c filename=loop_initialize_narrows_a_held_byte_range_without_a_count_bound.c
int32 count_up(uint8 *a, int32 n) {
    int32 steps = 0;
    for (int32 i = 0; i < n; i++) {
        steps = i;
    }
    return steps;
}
```

```click
verifying "loop_initialize_narrows_a_held_byte_range_without_a_count_bound.c";

int32 count_up(uint8 *a, int32 n) {
    views a[0..n];
    requires 0 <= n;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        invariant forall (k: int32) { 0 <= k and k <= n implies viewable(a[0..k]) };
        initialize by {
            have forall (k: int32) { 0 <= k and k <= n implies viewable(a[0..k]) } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k <= n);
                simp();
            }
            simp();
        }
        preserve by {
            step();
            step();
            have forall (k: int32) { 0 <= k and k <= n implies viewable(a[0..k]) } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k <= n);
                simp();
            }
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
pass
```
