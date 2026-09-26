# A quantified viewable invariant one prefix too wide is refused

The negative of
[`loop_initialize_narrows_a_held_range_under_a_universal.md`](loop_initialize_narrows_a_held_range_under_a_universal.md).
This invariant covers one prefix more than the loop has visited:
`forall (k: int32) { 0 <= k and k <= i + 1 implies viewable(a[0..k]) }`. It
holds on entry, where `k <= 1 <= n`, but once `i == n` it claims
`viewable(a[0..n + 1])`, and for `n == 1073741823` even its extent bound
`n + 1 <=u 1073741823` is false. The binder is bounded only by `i + 1`, which
`i <= n` and `n <= 1073741823` bound by `1073741824`, so the extent bound is
not decided for every `k` the invariant covers. The head assumes it as the
invariant's content, so it is owed where the invariant is established, and the
closer at the back edge is refused for it: the unproved bundle spells the
bound over the binder, `k <= 1073741823`.

```c filename=loop_quantified_viewable_invariant_one_prefix_too_wide_is_refused.c
int32 count_up(int32 *a, int32 n) {
    int32 steps = 0;
    for (int32 i = 0; i < n; i++) {
        steps = i;
    }
    return steps;
}
```

```click
verifying "loop_quantified_viewable_invariant_one_prefix_too_wide_is_refused.c";

int32 count_up(int32 *a, int32 n) {
    views a[0..n];
    requires 1 <= n;
    requires n <= 1073741823;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i;
        invariant i <= n;
        invariant forall (k: int32) { 0 <= k and k <= i + 1 implies viewable(a[0..k]) };
        initialize by {
            have forall (k: int32) { 0 <= k and k <= i + 1 implies viewable(a[0..k]) } by {
                intro();
                intro();
                extract(0 <= k);
                extract(k <= i + 1);
                simp();
            }
            simp();
        }
        preserve by {
            step();
            step();
            close_invariants();
        }
    }
    execute();
    simp();
}
```

```expect
fail: implies 0 <= k and k <= (i + 1) implies k <= 1073741823 }
```
