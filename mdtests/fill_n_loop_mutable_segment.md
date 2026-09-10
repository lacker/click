# fill_n declares its per-step owned segment

This checks that a symbolic pointer-writing loop can prove an explicit
one-body-step ownership clause. Direct loop-level `owns` clauses talk about the
whole loop span; the `step` block talks about one loop body step under the
current invariants and true loop condition, so it can use `i` in the segment
bounds.

```c filename=fill_n_loop_mutable_segment.c
int32 fill_n_loop_mutable_segment(int32 p[], int32 n) {
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
verifying "fill_n_loop_mutable_segment.c";

int32 fill_n_loop_mutable_segment(int32 p[], int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires loadable(p[0..n]);
    consumes p[0..n];
    ensures returns_n: result == n;
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
