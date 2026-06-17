# fill_tail does not implicitly frame the first cell

This checks that a pointer-writing loop does not get an implicit old-memory
frame theorem. The loop writes `p[i]` for `1 <= i < n`, and proving that
`p[0]` is unchanged needs an explicit two-state invariant or frame clause.

```c filename=fill_tail_preserves_first.c
int32 fill_tail_preserves_first(int32 p[], int32 n) {
    int32 i;
    i = 1;
    while (i < n) {
        p[i] = i;
        i = i + 1;
    }
    return i;
}
```

```click
verifying "fill_tail_preserves_first.c";

int32 fill_tail_preserves_first(int32 p[], int32 n) {
    requires n >= 1 and n <= 2147483647;
    requires valid_range(p, n * 4);
    at loop 0 {
        invariant i >= 1 and i <= n by auto;
    }
    ensures frame_and_result: p[0] == old(p[0]) and result == n by auto;
}
```

```expect
fail: left side evaluated
```
