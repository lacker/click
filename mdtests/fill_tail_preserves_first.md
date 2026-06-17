# fill_tail preserves the first cell through a symbolic pointer loop

This checks first-frame reasoning for a symbolic loop. The loop writes
`p[i]` for `1 <= i < n`, so `auto` should prove that `p[0]` is unchanged
without unrolling the loop.

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
pass
```
