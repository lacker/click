# A quantified viewable invariant over bytes is initialized by narrowing the held range

The `uint8` twin of `mdtests/loop_initialize_narrows_a_held_range_under_a_universal.md`.
A range of one-byte elements lowers its extent unscaled: `a[0..n]` is `n`
bytes, not `n * 1`. Range narrowing and the Surface spelling of a held range
both read an extent's element width off its scale factor, so a byte range
had no width, the held `views a[0..n]` had no written spelling to cite, and
`simp()` refused to narrow it to `viewable(a[0..k])`. An unscaled extent is
now read at byte granularity in both places, and the proof is the same as
over `int32`.

```c filename=loop_initialize_narrows_a_held_byte_range_under_a_universal.c
int32 count_up(uint8 *a, int32 n) {
    int32 steps = 0;
    for (int32 i = 0; i < n; i++) {
        steps = i;
    }
    return steps;
}
```

```click
verifying "loop_initialize_narrows_a_held_byte_range_under_a_universal.c";

int32 count_up(uint8 *a, int32 n) {
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
