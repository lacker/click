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
    requires loadable(p[0..n]);
    consumes p[0..n];
    ensures returns_n: result == n;
    ensures filled_segment: forall (k: int32) {
        0 <= k and k < n implies p[k] == k
    };
} by {
    step();
    step();
    loop as fill {
        invariant i >= 0 and i <= n;
        invariant forall (k: int32) {
            0 <= k and k < i implies p[k] == k
        };

        initialize by simp;
        preserve by {
            step();
            step();
            have i == at(statement(3).entry, i) + 1 by simp;
            simp();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
