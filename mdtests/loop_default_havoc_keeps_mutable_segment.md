# A clause-free loop still havocs a separately owned segment

The function owns `&g[0..1]`, so the segment is part of what the loop body may
write. Bounding the default loop havoc by ownership must not drop it: a
post-loop claim that `g` still holds its pre-loop value has to fail.

```c filename=loop_default_havoc_keeps_mutable_segment.c
int32 g = 0;

void loop_default_havoc_keeps_mutable_segment(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        g = i;
        i = i + 1;
    }
}
```

```click
verifying "loop_default_havoc_keeps_mutable_segment.c";

void loop_default_havoc_keeps_mutable_segment(int32 n) {
    requires n >= 0 and n <= 100;
    owns &g[0..1];
    ensures stale: g == old(g);
} by {
    step();
    step();
    loop {
        invariant i >= 0 and i <= n;
    }
    step();
    simp();
}
```

```expect
fail: loop_default_havoc_keeps_mutable_segment.stale
```
