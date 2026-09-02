# loop havoc carries a checked write set

This checks that a whole-loop mutable effect summary is carried through the
loop-havoc memory-DAG edge. The post-loop load of `p[0]` is not materialized at
loop entry, so the proof must transport it across the verified footprint rather
than rely on copy-back of an entry cell.

```c filename=loop_havoc_write_set.c
int32 loop_havoc_write_set(int32 p[], int32 n) {
    int32 i;
    i = 1;
    while (i < n) {
        p[i] = i;
        i = i + 1;
    }
    return p[0];
}
```

```click
verifying "loop_havoc_write_set.c";

int32 loop_havoc_write_set(int32 p[], int32 n) {
    requires n >= 1;
    requires n <= 100;
    requires loadable(p[0..n]);
    consumes p[0..n];
    ensures result == old(p[0]);
} by {
    step();
    step();
    loop {
        invariant i >= 1;
        invariant i <= n;
        mutable (p + 1)[0..n - 1] by frame;
    }
    step();
    simp();
}
```

```expect
pass
```
