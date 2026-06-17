# fill_tail proves a prefix frame with segment syntax

This checks that a memory-changing loop can prove an old-memory frame when that
frame fact is stated as a segment-preservation invariant. The prefix is outside
the write footprint.

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
    requires valid_range(p[0..n]);
    at loop 0 {
        invariant i >= 1 and i <= n by auto;
        invariant preserves(p[0..1]) by auto;
    }
    ensures prefix_preserved: preserves(p[0..1]) by auto;
}
```

```expect
pass
```
