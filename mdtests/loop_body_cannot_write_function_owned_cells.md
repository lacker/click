# A declaring loop's body cannot write what the function keeps

The loop declares ownership of `a[0..n]` only, so the function keeps
`object(b)`, and the body sees it only as a view. The store `b->x = 7` inside
the body is refused for want of ownership. This refusal is what lets a loop
head keep every cell the function keeps owning unchanged
(`mdtests/loop_keeps_cells_the_function_keeps_owning.md`): the body cannot
write one, even when the loop's footprint may cover it.

```c filename=loop_body_frame_write.c
struct box {
    int32 x;
    int32 y;
};

void fill(struct box* b, int32* a, int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        a[i] = 0;
        b->x = 7;
        i = i + 1;
    }
}
```

```click
verifying "loop_body_frame_write.c";

void fill(struct box* b, int32* a, int32 n) {
    owns object(b);
    owns a[0..n];
    requires 0 <= n;
    requires b->x == 3;
    ensures b->x == 3;
} by {
    step();
    step();
    loop {
        owns a[0..n];
        invariant 0 <= i and i <= n;
        invariant b->x == 3;
        decreases n - i;
        initialize by simp;
        preserve by {
            step();
            step();
            step();
            simp();
        }
    }
    execute();
    simp();
}
```

```expect
fail: missing resource fact `owns b[0..1]`
```
