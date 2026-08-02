# sort3 proves a three-cell permutation predicate

This checks that the explicit six-way fixed-size permutation claim can be
packaged as a named Click predicate and unfolded at the proof site.

```c filename=sort3_permutation_predicate.c
int32 sort3_permutation_predicate(int32 p[3]) {
    int32 tmp;
    if (p[1] < p[0]) {
        tmp = p[0];
        p[0] = p[1];
        p[1] = tmp;
    }
    if (p[2] < p[1]) {
        tmp = p[1];
        p[1] = p[2];
        p[2] = tmp;
    }
    if (p[1] < p[0]) {
        tmp = p[0];
        p[0] = p[1];
        p[1] = tmp;
    }
    return 0;
}
```

```click
verifying "sort3_permutation_predicate.c";

predicate permutation3(p: int32[], a: int32, b: int32, c: int32) {
    (p[0] == a and p[1] == b and p[2] == c)
    or
    (p[0] == a and p[1] == c and p[2] == b)
    or
    (p[0] == b and p[1] == a and p[2] == c)
    or
    (p[0] == b and p[1] == c and p[2] == a)
    or
    (p[0] == c and p[1] == a and p[2] == b)
    or
    (p[0] == c and p[1] == b and p[2] == a)
}

int32 sort3_permutation_predicate(int32 p[3]) {
    requires loadable(p[0..3]);
    consumes p[0..3];
    ensures permutation: permutation3(p, old(p[0]), old(p[1]), old(p[2])) by {
        execute();
        unfold(permutation3);
        simp();
    }
}
```

```expect
pass
```
