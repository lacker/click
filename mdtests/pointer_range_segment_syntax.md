# pointer range segment syntax

This checks that Click-side C-reference syntax can spell a loadable range as a
half-open element segment.

```c filename=pointer_range_segment_syntax.c
int32 fill_n_with_segment_range(int32 p[], int32 n) {
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
verifying "pointer_range_segment_syntax.c";

int32 fill_n_with_segment_range(int32 p[], int32 n) {
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
