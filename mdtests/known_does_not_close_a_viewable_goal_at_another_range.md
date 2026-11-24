# `close()` does not close a `viewable` goal from a wider range

`close()` closes a goal only from the identical available fact
(`mdtests/known_closes_an_established_viewable_fact.md`). `viewable(a[0..n])`
is not `viewable(a[0..k])`: narrowing one to the other is `transport … using`,
which checks the order facts that place `0..k` inside `0..n`. `close()`
does not narrow.

```c filename=known_does_not_close_a_viewable_goal_at_another_range.c
int32 probe(int32 a[], int32 n, int32 k) {
    return 0;
}
```

```click checked-only
verifying "known_does_not_close_a_viewable_goal_at_another_range.c";

int32 probe(int32 a[], int32 n, int32 k) {
    requires 0 <= k;
    requires k <= n;
    requires n <= 1073741823;
    views a[0..n];
    ensures result == 0;
} by {
    step();
    have viewable(a[0..n]) by {
        close();
    }
    have viewable(a[0..k]) by close();
    close();
}
```

```expect
fail: `known` requires the current goal as an available semantic fact: current goal is a memory-viewability fact
```
