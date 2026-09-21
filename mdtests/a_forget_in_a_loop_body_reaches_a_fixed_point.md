# a loop body that forgets a cell every iteration still settles

Each iteration writes `a[k]` at an index not provably distinct from the one the
previous iteration wrote, so each iteration drops the cell the last one left and
marks the snapshot it dropped it from. A mark that added one link per iteration
without the loop-head state ever repeating would leave the loop without a fixed
point. This fixture is the standing check that it settles and that the ordinary
loop proof still goes through.

```c filename=a_forget_in_a_loop_body_reaches_a_fixed_point.c
void fill_prefix(int32 a[], int32 n) {
    for (int32 k = 0; k < n; k++) {
        a[k] = 7;
    }
}
```

```click
verifying "a_forget_in_a_loop_body_reaches_a_fixed_point.c";

void fill_prefix(int32 a[], int32 n) {
    requires 0 <= n;
    requires n <= 1073741823;
    consumes a[0..n];
    produces a[0..n];
} by {
    step();
    step();
    loop {
        decreases n - k;
        invariant 0 <= k;
        invariant k <= n;
        owns a[0..n];
        initialize by { simp(); }
        preserve by {
            step();
            step();
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
