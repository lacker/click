# A growing viewable prefix owes its extent at the back edge

`viewable(a[0..i])` as a loop invariant also states that `a[0..i]` is a valid
32-bit byte extent: `0 <= i` and, for four-byte elements, `i <= 1073741823`.
That half is ordinary invariant content. The head assumes it with the range,
and the entry and every back edge owe it with the range.

Here `n` is unbounded above and the held range is the constant `a[0..8]`, so
after `i = i + 1` nothing bounds `i` by `1073741823` and the back edge is
refused, with the extent bound spelled as a proof would write it. This loop
used to be refused at the head instead, as a missing prerequisite the head
demanded before it would assume the invariant.

```c filename=loop_invariant_viewable_prefix_owes_its_extent_at_the_back_edge.c
int32 walk(int32 *a, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_invariant_viewable_prefix_owes_its_extent_at_the_back_edge.c";

int32 walk(int32 *a, int32 n) {
    views a[0..8];
    requires 0 <= n;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        invariant viewable(a[0..i]);
    }
    step();
    simp();
}
```

```expect
fail: goal: i <= 1073741823 and ((i <= 1073741823 implies viewable(a[0..i]))
```
