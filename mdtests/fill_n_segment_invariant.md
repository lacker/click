# fill_n proves a quantified written segment

This checks that a memory-changing symbolic loop can use a quantified loop
invariant to describe the segment that has already been written.

```c filename=fill_n_segment_invariant.c
int32 fill_n_segment_invariant(int32 p[], int32 n) {
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
verifying "fill_n_segment_invariant.c";

int32 fill_n_segment_invariant(int32 p[], int32 n) {
    requires n >= 0 and n <= 2147483647;
    requires valid_range(p, n * 4);
    loop 0 {
        invariant i >= 0 and i <= n by auto;
        invariant forall (int32 k) {
            0 <= k and k < i implies p[k] == k
        } by auto;
    }
    ensures returns_n: result == n by auto;
    ensures filled_segment: forall (int32 k) {
        0 <= k and k < n implies p[k] == k
    } by auto;
}
```

```expect
pass
```
