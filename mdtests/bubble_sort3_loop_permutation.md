# bubble_sort3_loop preserves the three-cell permutation

This checks that the loop-shaped fixed-size bubble sort still preserves the
explicit six-way permutation of the original three cells.

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
