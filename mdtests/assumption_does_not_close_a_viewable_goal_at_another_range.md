# `assumption()` does not close a `viewable` goal from a wider range

`assumption()` closes a goal only from the identical available fact
(`mdtests/assumption_closes_an_established_viewable_fact.md`). `viewable(a[0..n])`
is not `viewable(a[0..k])`: narrowing one to the other is `transport … using`,
which checks the order facts that place `0..k` inside `0..n`. `assumption()`
does not narrow.

```c filename=assumption_does_not_close_a_viewable_goal_at_another_range.c
int32 probe(int32 a[], int32 n, int32 k) {
    return 0;
}
```

```click
verifying "assumption_does_not_close_a_viewable_goal_at_another_range.c";

int32 probe(int32 a[], int32 n, int32 k) {
    requires 0 <= k;
    requires k <= n;
    requires n <= 1073741823;
    views a[0..n];
    ensures result == 0;
} by {
    step();
    have viewable(a[0..n]) by { simp(); }
    have viewable(a[0..k]) by { assumption(); }
    simp();
}
```

```expect
fail: `assumption` requires the current goal as an available semantic fact: current goal is a memory-viewability fact
```
