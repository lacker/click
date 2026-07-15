# compare_swap2 proves the stdlib two-cell permutation

This checks that a conditional swap can prove the output pair is a permutation
of the entry-state pair using the standard `permutation` predicate.

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
    requires loadable(p[0..2]);
    consumes p[0..2];
    ensures pair_permutation: permutation(p, old(p), 0, 2) by {
        execute_rest();
        unfold(permutation);
        simp();
    }
}
```

```expect
pass
```
