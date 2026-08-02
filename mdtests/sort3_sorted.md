# sort3 sorts three cells

This checks the fixed-size sorting target before introducing nested loops:
three compare-swap steps should leave `p[0..3]` nondecreasing.

```c filename=sort3.c
int32 sort3(int32 p[3]) {
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
verifying "sort3.c";

predicate sorted(p: int32[], n: int32) {
    sorted_range(p, 0, n)
}

predicate sorted_range(p: int32[], lo: int32, hi: int32) {
    forall (i: int32) {
        forall (j: int32) {
            0 <= i and 0 <= j and lo <= i and i < j and j < hi implies p[i] <= p[j]
        }
    }
}

int32 sort3(int32 p[3]) {
    requires loadable(p[0..3]);
    consumes p[0..3];
    ensures sorted: sorted(p, 3) by {
        execute();
        unfold(sorted);
        unfold(sorted_range);
    }
}
```

```expect
pass
```
