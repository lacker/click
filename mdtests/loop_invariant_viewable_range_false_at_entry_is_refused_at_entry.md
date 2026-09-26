# A viewable-range invariant whose extent is false at entry is refused at entry

The loop head assumes the extent half of a stated range, `0 <= k` for
`viewable(a[0..k])`, as invariant content. That is sound only because the
entry owes it. Here `k` is `-1` on entry, so `a[0..-1]` runs backwards and the
invariant is false before the first iteration. Its lowering at the entry state
has no reading at all: it prunes a range it already decides is not an extent.
An invariant with no reading must owe the impossible goal rather than nothing,
or the head's `0 <= k` would be assumed with nobody having proved it, and the
false `ensures result >= 0` would follow at the exit.

The body keeps `k` loop-modified so the head reads it as an unknown value; the
C is synthetic.

```c filename=loop_invariant_viewable_range_false_at_entry_is_refused_at_entry.c
int32 walk(int32 *a, int32 n) {
    int32 k;
    int32 i;
    k = -1;
    i = 0;
    while (i < n) {
        i = i + 1;
        k = k * 1;
    }
    return k;
}
```

```click
verifying "loop_invariant_viewable_range_false_at_entry_is_refused_at_entry.c";

int32 walk(int32 *a, int32 n) {
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
fail: loop 0 invariant 2 entry: this invariant cannot hold here: a memory range it states runs backwards, so it is not a byte extent: its end is 1 element before its start
```
