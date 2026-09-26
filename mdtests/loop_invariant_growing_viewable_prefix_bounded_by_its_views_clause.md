# A growing viewable prefix takes its extent bound from the `views` clause

[`loop_invariant_states_a_growing_viewable_prefix.md`](loop_invariant_states_a_growing_viewable_prefix.md)
without `requires n <= 1073741823`. The contract's `views a[0..n]` states a
range, and a stated range carries its extent half as a fact beside it
(`docs/concepts/viewability.md`): here `0 <= n` and `n <= 1073741823`. The loop
head already read that bound. The back edge did not: its closer cites only the
premises the loop head and the contract name, the written `requires` among
them, and the `views` clause's extent half was not one of them, so the extent
bound of `viewable(a[0..i])` for the new `i` was refused. The closer now names
the extent half of every range the contract states, in the spelling a proof
can write, and keeps it only where it is exactly available.

```c filename=loop_invariant_growing_viewable_prefix_bounded_by_its_views_clause.c
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
verifying "loop_invariant_growing_viewable_prefix_bounded_by_its_views_clause.c";

int32 any_zero(int32 *a, int32 n) {
    views a[0..n];
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
pass
```
