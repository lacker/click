# A growing viewable prefix still owes its extent bound

The negative of
[`loop_invariant_states_a_growing_viewable_prefix.md`](loop_invariant_states_a_growing_viewable_prefix.md).
Here nothing bounds `n`: the contract views a fixed eight cells and says only
`0 <= n`. The loop head reads `viewable(a[0..i])` with `i < n`, and `n` may be
as large as `2147483647`, so `i` is not known to be a valid four-byte element
count — at `i == 1 << 30` the extent `i * 4` wraps to zero. Deciding the
unsigned extent bound from signed order facts needs both `0 <= i` and an upper
bound at or below `1073741823`; the lower bound alone is refused.

```c filename=loop_invariant_growing_viewable_prefix_needs_its_extent_bound.c
int32 any_zero(int32 *a, int32 n) {
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
verifying "loop_invariant_growing_viewable_prefix_needs_its_extent_bound.c";

int32 any_zero(int32 *a, int32 n) {
    views a[0..8];
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
fail: loop-head prerequisite
```
