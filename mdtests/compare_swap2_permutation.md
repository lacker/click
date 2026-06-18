# compare_swap2 preserves the two-cell permutation

This checks that a conditional swap can prove the output pair is either the
original pair or the swapped original pair.

```c filename=compare_swap2_permutation.c
int32 compare_swap2_permutation(int32 p[2]) {
    int32 tmp;
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
verifying "compare_swap2_permutation.c";

int32 compare_swap2_permutation(int32 p[2]) {
    requires valid_range(p[0..2]);
    ensures pair_permutation:
        (p[0] == old(p[0]) and p[1] == old(p[1]))
        or
        (p[0] == old(p[1]) and p[1] == old(p[0]))
        by auto;
}
```

```expect
pass
```
