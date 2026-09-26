# A growing viewable prefix does not borrow another range's extent

The negative of
[`loop_invariant_growing_viewable_prefix_bounded_by_its_views_clause.md`](loop_invariant_growing_viewable_prefix_bounded_by_its_views_clause.md).
The contract views `a[0..m]`, so its extent half bounds `m`, and nothing
relates `m` to the loop bound `n`. The invariant `viewable(a[0..i])` with
`i <= n` is then false whenever `n > m`, and even its extent bound fails for
`n` past `1073741823`. The head assumes the invariant's own extent half, which
the back edge would owe, but the `views` clause's `m <= 1073741823` is about
`m` only and says nothing about the cell `a[i]` the body reads, so the body is
refused at that read.

```c filename=loop_invariant_viewable_prefix_does_not_borrow_another_ranges_extent.c
int32 any_zero(int32 *a, int32 n, int32 m) {
    int32 found = 0;
    for (int32 i = 0; i < n; i++) {
        if (a[i] == 0) {
            found = 1;
        }
    }
    return found;
}
```

```click
verifying "loop_invariant_viewable_prefix_does_not_borrow_another_ranges_extent.c";

int32 any_zero(int32 *a, int32 n, int32 m) {
    views a[0..m];
    requires 0 <= m;
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
        invariant viewable(a[0..i]);
    }
    execute();
    simp();
}
```

```expect
fail: missing resource fact `views a[i..(i + 1)]`
```
