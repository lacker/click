# A loop with no effect clause frames viewed memory

The loop body writes `p[i]`, which the function owns. It cannot write `r`,
which the function only views, so the default loop footprint is the owned
range and the viewed cell is framed across the loop with no whole-loop effect
clause and no invariant naming `r`.

```c filename=loop_default_havoc_frames_viewed_memory.c
void loop_default_havoc_frames_viewed_memory(int32 p[], int32 r[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        p[i] = i;
        i = i + 1;
    }
}
```

```click
verifying "loop_default_havoc_frames_viewed_memory.c";

void loop_default_havoc_frames_viewed_memory(int32 p[], int32 r[], int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires loadable(p[0..n]);
    requires loadable(r[0..1]);
    owns p[0..n];
    views r[0..1];
    requires separate(memory(p[0..n]), memory(r[0..1]));
    ensures r_preserved: r[0] == old(r[0]);
} by {
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= n;
    }
    step();
    simp();
}
```

```expect
pass
```
