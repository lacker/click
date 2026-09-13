# A partial borrow leaves the neighboring cell writable

The reader borrows the first cell and owns the second cell it updates. The
two ranges are disjoint, so the caller can lend the read range while retaining
the write range.

```c filename=stable_view_partial_borrow.c
int32 stable_view_partial_borrow(int32 p[]) {
    int32 first;
    first = p[0];
    p[1] = first + 1;
    return p[1];
}
```

```click
verifying "stable_view_partial_borrow.c";

int32 stable_view_partial_borrow(int32 p[]) {
    requires p[0] < 2147483647;
    views p[0..1];
    owns p[1..2];
    ensures result == old(p[0]) + 1;
} by {
    execute();
    simp();
}
```

```expect
pass
```
