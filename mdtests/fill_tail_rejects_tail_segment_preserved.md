# fill_tail rejects a false quantified tail frame

This checks that the loop frame proof does not claim preservation for a segment
that overlaps the loop write footprint.

```c filename=fill_tail_rejects_tail_segment_preserved.c
int32 fill_tail_rejects_tail_segment_preserved(int32 p[], int32 n) {
    int32 i;
    i = 1;
    while (i < n) {
        p[i] = i;
        i = i + 1;
    }
    return n;
}
```

```click
verifying "fill_tail_rejects_tail_segment_preserved.c";

int32 fill_tail_rejects_tail_segment_preserved(int32 p[], int32 n) {
    requires n >= 2 and n <= 2147483647;
    requires valid_range(p, n * 4);
    loop 0 {
        invariant i >= 1 and i <= n by auto;
    }
    ensures tail_preserved: forall (int32 k) {
        1 <= k and k < n implies p[k] == old(p[k])
    } by auto;
}
```

```expect
fail: proposition was not provable
```
