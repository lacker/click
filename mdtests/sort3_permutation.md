# sort3 preserves the three-cell permutation

This checks the explicit six-way permutation claim for fixed-size sorting. It is
intentionally verbose: this is the baseline before introducing better notation
for multisets or permutation predicates.

```c filename=sort3_permutation.c
int32 sort3_permutation(int32 p[3]) {
    int32 tmp;
    if (p[1] < p[0]) {
        tmp = p[0];
        p[0] = p[1];
        p[1] = tmp;
    } else {
        p[0] = p[0];
    }
    if (p[2] < p[1]) {
        tmp = p[1];
        p[1] = p[2];
        p[2] = tmp;
    } else {
        p[1] = p[1];
    }
    if (p[1] < p[0]) {
        tmp = p[0];
        p[0] = p[1];
        p[1] = tmp;
    } else {
        p[0] = p[0];
    }
    return 0;
}
```

```click
verifying "sort3_permutation.c";

int32 sort3_permutation(int32 p[3]) {
    requires valid_range(p[0..3]);
    ensures permutation:
        (p[0] == old(p[0]) and p[1] == old(p[1]) and p[2] == old(p[2]))
        or
        (p[0] == old(p[0]) and p[1] == old(p[2]) and p[2] == old(p[1]))
        or
        (p[0] == old(p[1]) and p[1] == old(p[0]) and p[2] == old(p[2]))
        or
        (p[0] == old(p[1]) and p[1] == old(p[2]) and p[2] == old(p[0]))
        or
        (p[0] == old(p[2]) and p[1] == old(p[0]) and p[2] == old(p[1]))
        or
        (p[0] == old(p[2]) and p[1] == old(p[1]) and p[2] == old(p[0]))
        by auto;
}
```

```expect
pass
```
