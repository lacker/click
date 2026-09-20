# a loop body's store does not preserve an invariant about a symbolic cell

The loop writes `a[i]` and the invariant is about `a[m]`, with nothing saying
the two indexes differ. The invariant is not preserved, and the body cannot
establish it.

```c filename=loop_invariant_on_a_symbolic_cell_is_not_free.c
void mark_prefix(int32 a[], int32 n, int32 m) {
    for (int32 i = 0; i < n; i++) {
        a[i] = 1;
    }
}
```

```click
verifying "loop_invariant_on_a_symbolic_cell_is_not_free.c";

void mark_prefix(int32 a[], int32 n, int32 m) {
    requires 0 <= n;
    requires 0 <= m;
    requires m < n;
    requires n <= 1073741823;
    requires a[m] == 7;
    consumes a[0..n];
    produces a[0..n];
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        invariant a[m] == 7;
        owns a[0..n];
        initialize by { simp(); }
        preserve by {
            step();
            have a[m] == 7 by { simp(); }
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
fail: `a[m]` in the goal and `a[m]` in an available fact may be different reads
```
