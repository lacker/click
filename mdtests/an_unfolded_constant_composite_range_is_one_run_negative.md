# A store into an unfolded composite run may have written a symbolic element

The negative of `an_unfolded_constant_composite_range_is_one_run.md`. The
store writes element `3` of the run the unfold exposed, and `k` may be `3`,
so the element `k` read afterwards is not known to hold its old value.

```c filename=an_unfolded_constant_composite_range_is_one_run_negative.c
int32 put_then_read(int32 *a, int32 k) {
    a[3] = 5;
    return a[k];
}
```

```click
verifying "an_unfolded_constant_composite_range_is_one_run_negative.c";

resource block(p: int32*) { owns p[0..1000]; }

int32 put_then_read(int32 *a, int32 k) {
    owns block(a);
    requires 0 <= k;
    requires k < 1000;
    ensures result == old(a[k]);
} by {
    unfold(block(a));
    step_until(function.exit);
    fold(block(a));
    close();
}
```

```expect
fail: the store to `a[3]` may have written it
```
