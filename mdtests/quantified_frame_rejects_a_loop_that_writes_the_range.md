# a loop havoc is not framed by the quantified guard

The loop writes every cell of `a[0..n]`, and its write set is bounded only
by its own clauses. The entry values of `a` do not survive it, so the
quantified frame across the loop is refused.

```c filename=quantified_frame_rejects_a_loop_that_writes_the_range.c
void wipe(int32 a[], int32 n) {
    for (int32 i = 0; i < n; i++) {
        a[i] = 1;
    }
}
```

```click
verifying "quantified_frame_rejects_a_loop_that_writes_the_range.c";

void wipe(int32 a[], int32 n) {
    requires 0 < n;
    requires n <= 1073741823;
    owns a[0..n];
    ensures forall (k: int32) { 0 <= k and k < n implies a[k] == old(a[k]) };
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        owns a[0..n];
        initialize by { close(); }
        maintain by {
            step();
            step();
        }
    }
    have forall (k: int32) { 0 <= k and k < n implies a[k] == old(a[k]) } by { close(); }
}
```

```expect
fail: `solve` failed
```
