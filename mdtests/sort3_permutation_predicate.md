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
verifying "sort3_permutation_predicate.c";

predicate permutation3(int32 p[], int32 a, int32 b, int32 c) {
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
    requires valid_range(p[0..3]);
    requires write(p[0..3]);
    ensures permutation: permutation3(p, old(p[0]), old(p[1]), old(p[2])) by {
        symbolic_execute();
        unfold(permutation3);
        simp();
        close();
    }
}
```

```expect
pass
```
