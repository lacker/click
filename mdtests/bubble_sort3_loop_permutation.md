# bubble_sort3_loop preserves the three-cell permutation

This checks that the loop-shaped fixed-size bubble sort preserves the
standard-library permutation predicate over the entry-state cells.

```c filename=bubble_sort3_loop_permutation.c
int32 bubble_sort3_loop_permutation(int32 p[3]) {
    int32 i;
    int32 j;
    int32 tmp;
    i = 0;
    while (i < 3) {
        j = 0;
        while (j < 2) {
            if (p[j + 1] < p[j]) {
                tmp = p[j];
                p[j] = p[j + 1];
                p[j + 1] = tmp;
            } else {
                p[j] = p[j];
            }
            j = j + 1;
        }
        i = i + 1;
    }
    return 0;
}
```

```click
verifying "bubble_sort3_loop_permutation.c";

int32 bubble_sort3_loop_permutation(int32 p[3]) {
    requires loadable(p[0..3]);
    consumes p[0..3];
    ensures permutation: permutation(p, old(p), 0, 3) by {
        bounded_execute();
        unfold(permutation);
        simp();
    }
}
```

```expect
pass
```
