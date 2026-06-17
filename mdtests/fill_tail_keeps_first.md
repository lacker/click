# fill_tail keeps the first cell with an old-state invariant

This checks that a pointer-writing loop can prove an old-memory frame theorem
when the frame fact is stated explicitly as a loop invariant. The loop writes
`p[i]` for `1 <= i < n`, so the invariant proves `p[0]` is unchanged.

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
    requires valid_range(p, n * 4);
    loop 0 {
        invariant i >= 1 and i <= n by auto;
        invariant p[0] == old(p[0]) by auto;
    }
    ensures frame_and_result: p[0] == old(p[0]) and result == n by auto;
}
```

```expect
pass
```
