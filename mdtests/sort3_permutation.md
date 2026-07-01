# sort3 preserves the stdlib three-cell permutation

This checks that the standard-library `permutation` predicate can prove a
three-cell sorting network preserves the entry-state multiset.

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
    requires write(p[0..3]);
    ensures permutation: permutation(p, old(p), 0, 3) by {
        symbolic_execute();
        unfold(permutation);
        simp();
    }
}
```

```expect
pass
```
