# compare_swap2 proves a sorted_pair predicate

This checks that a predicate goal can be unfolded into its body during an
explicit deterministic proof script.

```c filename=compare_swap2_sorted_predicate.c
int32 compare_swap2_sorted_predicate(int32 p[2]) {
    int32 tmp;
    if (p[1] < p[0]) {
        tmp = p[0];
        p[0] = p[1];
        p[1] = tmp;
    } else {
        tmp = 0;
    }
    return 0;
}
```

```click
verifying "compare_swap2_sorted_predicate.c";

predicate sorted_pair(int32 p[2]) {
    p[0] <= p[1]
}

int32 compare_swap2_sorted_predicate(int32 p[2]) {
    requires loadable(p[0..2]);
    consumes p[0..2];
    ensures sorted: sorted_pair(p) by {
        symbolic_execute();
        unfold(sorted_pair);
        simp();
    }
}
```

```expect
pass
```
