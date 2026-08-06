# fill_n declares its mutable target segment

This checks that a symbolic pointer-writing loop can prove a compact effect
clause describing the only external memory segment it may mutate.

```c filename=fill_n_mutable_segment.c
int32 fill_n_mutable_segment(int32 p[], int32 n) {
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
verifying "fill_n_mutable_segment.c";

int32 fill_n_mutable_segment(int32 p[], int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires loadable(p[0..n]);
    consumes p[0..n];
    mutable p[0..n];
    ensures returns_n: result == n;
} by {
    step();
    step();
    loop {
        invariant i >= 0;
        invariant i <= n;
        mutable p[0..n] by frame;
    }
    step();
    frame();
    simp();
}
```

```expect
pass
```
