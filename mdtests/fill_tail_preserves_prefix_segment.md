# fill_tail proves a quantified prefix frame

This checks that a memory-changing loop can prove a quantified frame
postcondition for a segment that is outside the loop write footprint.

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
pass
```
