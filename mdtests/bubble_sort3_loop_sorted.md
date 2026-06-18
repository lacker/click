# bubble_sort3_loop sorts three cells

This checks the loop-shaped fixed-size sorting target: a concrete two-loop
bubble sort over three cells should leave `p[0..3]` nondecreasing.

```c filename=bubble_sort3_loop.c
int32 bubble_sort3_loop(int32 p[3]) {
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
verifying "bubble_sort3_loop.c";

int32 bubble_sort3_loop(int32 p[3]) {
    requires valid_range(p[0..3]);
    ensures sorted: p[0] <= p[1] and p[1] <= p[2] by auto;
}
```

```expect
pass
```
