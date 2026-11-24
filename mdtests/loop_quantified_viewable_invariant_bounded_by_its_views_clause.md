# A quantified viewable invariant takes its span bound from the `views` clause

[`loop_initialize_narrows_a_held_range_under_a_universal.md`](loop_initialize_narrows_a_held_range_under_a_universal.md)
without `requires n <= 1073741823`. At the back edge the span member
`forall (k: int32) { 0 <= k and k <= n implies (k as uint32) <= 1073741823u32 }`
needs `n <= 1073741823`, and the only clause that says so is `views a[0..n]`,
whose span half is a fact beside the range it states. The closer cites that
half as it cites a written precondition.

```c filename=loop_quantified_viewable_invariant_bounded_by_its_views_clause.c
int32 count_up(int32 *a, int32 n) {
    int32 steps = 0;
    for (int32 i = 0; i < n; i++) {
        steps = i;
    }
    return steps;
}
```

```click
verifying "loop_quantified_viewable_invariant_bounded_by_its_views_clause.c";

int32 count_up(int32 *a, int32 n) {
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
        invariant forall (k: int32) { 0 <= k and k <= n implies viewable(a[0..k]) };
        initialize by {
            have forall (k: int32) { 0 <= k and k <= n implies viewable(a[0..k]) } by {
                intro();
                intro();
                close();
            }
            close();
        }
        maintain by {
            step();
            step();
            have forall (k: int32) { 0 <= k and k <= n implies viewable(a[0..k]) } by {
                intro();
                intro();
                close();
            }
        }
    }
}
```

```expect
pass
```
