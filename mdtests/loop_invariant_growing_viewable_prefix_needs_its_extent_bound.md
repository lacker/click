# A growing viewable prefix over an unbounded count is refused

The negative of
[`loop_invariant_states_a_growing_viewable_prefix.md`](loop_invariant_states_a_growing_viewable_prefix.md).
Here nothing bounds `n`: the contract views a fixed eight cells and says only
`0 <= n`. The invariant `viewable(a[0..i])` carries its extent half, `0 <= i`
and `i <= 1073741823`, as content: the head assumes it, and the entry and each
back edge owe it. With `n` as large as `2147483647` the back edge could not
establish it, but the body is refused before that: it reads `a[i]` for every
`i < n`, and only `a[0..8]` is viewed, so the read is not covered. The loop used
to be refused at the head, which demanded the extent as a prerequisite before
it would assume the invariant.

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
fail: missing resource fact `views a[i..(i + 1)]`
```
