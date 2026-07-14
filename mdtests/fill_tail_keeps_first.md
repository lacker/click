# fill_tail keeps the first cell with an old-state invariant

This checks that a pointer-writing loop can prove an old-memory theorem when
the unchanged-memory fact is stated explicitly as a loop invariant. The loop
writes `p[i]` for `1 <= i < n`, so the invariant proves `p[0]` is unchanged.

```c filename=fill_tail_keeps_first.c
int32 fill_tail_keeps_first(int32 p[], int32 n) {
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
verifying "fill_tail_keeps_first.c";

int32 fill_tail_keeps_first(int32 p[], int32 n) {
    requires n >= 1 and n <= 2147483647;
    requires loadable(p, n * 4);
    requires write(p[0..n]);
    for loop(0) {
        invariant i >= 1 and i <= n;
        invariant p[0] == old(p[0]);
    }
    ensures frame_and_result: p[0] == old(p[0]) and result == n by auto;
}
```

```expect
pass
```
