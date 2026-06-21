# compare_swap2 proves the stdlib two-cell permutation

This checks that a conditional swap can prove the output pair is a permutation
of a copied snapshot array using the standard `permutation` predicate.

```c filename=compare_swap2_permutation.c
int32 compare_swap2_permutation(int32 p[2], int32 original[2]) {
    int32 tmp;
    original[0] = p[0];
    original[1] = p[1];
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

int32 compare_swap2_permutation(int32 p[2], int32 original[2]) {
    requires valid_range(p[0..2]);
    requires valid_range(original[0..2]);
    requires disjoint(p[0..2], original[0..2]);
    ensures pair_permutation: permutation(p, original, 0, 2) by {
        symbolic_execute();
        unfold(permutation);
        simp();
        close();
    }
}
```

```expect
pass
```
