# fill_n declares its per-iteration mutable segment

This checks that a symbolic pointer-writing loop can prove a per-iteration
effect clause. The function-level mutable clause talks about the whole call;
this loop-level clause talks about one loop body step under the current
invariants and true loop condition, so it can use `i` in the segment bounds.

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
    requires valid_range(p[0..n]);
    loop 0 {
        invariant i >= 0 by auto;
        invariant i <= n by auto;
        mutable p[i..i + 1] by auto;
    }
    ensures returns_n: result == n by auto;
}
```

```expect
pass
```
