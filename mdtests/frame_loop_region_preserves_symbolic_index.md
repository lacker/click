# frame loop region preserves a symbolic index

This checks that `frame(loop(0))` in an ensures proof certifies a
memory-preservation goal from the loop's `mutable` effect summary. The loop
writes `p[0..n]`, so `p[n]` keeps its entry-state value. With a symbolic
preserved index the closing `simp` cannot certify `p[n] == old(p[n])` on its
own, so the qualified frame carries the proof.

```c filename=frame_loop_region_preserves_symbolic_index.c
int32 frame_loop_region_preserves_symbolic_index(int32 p[], int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        p[i] = i;
        i = i + 1;
    }
    return i;
}
```

```click
verifying "frame_loop_region_preserves_symbolic_index.c";

int32 frame_loop_region_preserves_symbolic_index(int32 p[], int32 n) {
    requires n >= 0;
    requires n <= 100;
    requires loadable(p[0..n + 1]);
    consumes p[0..n + 1];
    ensures preserved: p[n] == old(p[n]);
} by {
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= n;
        mutable p[0..n] by frame;
        initialize by simp;
        preserve by {
            step();
            step();
            close_invariants();
        }
    }
    step();
    frame(loop(0));
    simp();
}
```

```expect
pass
```
