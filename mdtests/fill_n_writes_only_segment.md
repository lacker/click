# fill_n writes only its target segment

This checks that a symbolic pointer-writing loop can prove a compact frame
postcondition describing where its writes occur.

```c filename=fill_n_writes_only_segment.c
int32 fill_n_writes_only_segment(int32 p[], int32 n) {
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
verifying "fill_n_writes_only_segment.c";

int32 fill_n_writes_only_segment(int32 p[], int32 n) {
    requires n >= 0;
    requires n <= 2147483647;
    requires valid_range(p[0..n]);
    loop 0 {
        invariant i >= 0 by auto;
        invariant i <= n by auto;
    }
    ensures writes_segment: writes_only(p[0..n]) by auto;
}
```

```expect
pass
```
