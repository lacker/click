# fill_n frames its target segment by ownership

This checks that a symbolic pointer-writing loop frames by the memory the
function owns, with no effect clause and no framing tactic.

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
