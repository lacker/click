# A viewable-range invariant whose extent is false at the back edge is refused

The back-edge counterpart of
[`loop_invariant_viewable_range_false_at_entry_is_refused_at_entry.md`](loop_invariant_viewable_range_false_at_entry_is_refused_at_entry.md).
The head assumes `0 <= k`, the extent half of `viewable(a[0..k])`, which holds
at entry where `k` is `0`. The body then sets `k` to `-1`, so at the back edge
`a[0..-1]` runs backwards and the invariant is false. Were the back edge to owe
nothing for an invariant it cannot read, the head's `0 <= k` would carry the
false `ensures result >= 0` through the exit.

```c filename=loop_invariant_viewable_range_false_at_the_back_edge_is_refused.c
int32 walk(int32 *a, int32 n) {
    int32 k;
    int32 i;
    k = 0;
    i = 0;
    while (i < n) {
        i = i + 1;
        k = -1;
    }
    return k;
}
```

```click
verifying "loop_invariant_viewable_range_false_at_the_back_edge_is_refused.c";

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
fail: a memory range runs backwards, so it is not a byte extent: its end is 1 element before its start
```
