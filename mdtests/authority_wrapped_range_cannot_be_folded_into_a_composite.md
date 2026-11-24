# A range whose span wraps cannot be folded into a composite

A composite's contained ranges are stated ranges, so their byte-count guards
are available while the body's own `fact` clauses are evaluated. That is sound
only because no composite can be held at a range whose span wraps. A fold
must lower the body's facts against the instantiated arguments, and a
decidably invalid span leaves no lowering path.

This is a companion of `wrapped_range_cannot_reach_a_composite.md`, which
observes such a composite at a contract entry. An ordinary family has no count
witness. Its entry stays vacuous, because no caller can hold the composite:
the fold that would create one is refused here.

```c filename=wrapped_fold.c
int32 wrapped_fold(int32* p, int32 n) {
    return 0;
}
```

```click
resource slice_of(p: int32*, n: int32) {
    views p[0..n];
    fact viewable(p[0..n]);
}

verifying "wrapped_fold.c";

int32 wrapped_fold(int32* p, int32 n) {
    views p[0..n] as input;
    requires n == 1073741824;
    requires 0 < n;
    produces slice_of(p, n) from input;
} by {
    step_until(function.exit);
    fold(slice_of(p, n));
    close();
}
```

```expect
fail: the kernel lowering produced no path: a memory range is too wide to be a 32-bit byte span
```
