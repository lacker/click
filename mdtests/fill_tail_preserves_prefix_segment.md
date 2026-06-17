# fill_tail does not implicitly prove a quantified prefix frame

This checks that a memory-changing loop does not get an implicit quantified
old-memory frame theorem. The prefix is outside the write footprint, but
proving that needs an explicit two-state invariant or frame clause.

```c filename=fill_tail_preserves_prefix_segment.c
int32 fill_tail_preserves_prefix_segment(int32 p[], int32 n) {
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
verifying "fill_tail_preserves_prefix_segment.c";

int32 fill_tail_preserves_prefix_segment(int32 p[], int32 n) {
    requires n >= 1 and n <= 2147483647;
    requires valid_range(p, n * 4);
    at loop 0 {
        invariant i >= 1 and i <= n by auto;
    }
    ensures prefix_preserved: forall (int32 k) {
        0 <= k and k < 1 implies p[k] == old(p[k])
    } by auto;
}
```

```expect
fail: proposition was not provable
```
