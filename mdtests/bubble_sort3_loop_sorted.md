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

int32 bubble_sort3_loop(int32 p[3]) {
    requires loadable(p[0..3]);
    consumes p[0..3];
    ensures sorted: sorted(p, 3) by {
        step();
        step();
        step();
        step();
        step();
        step();
        step();
        if at(function.entry, p[1]) < at(function.entry, *p) {
            step();
            step();
            step();
            step();
            step();
            step();
            if at(function.entry, p[2]) < at(function.entry, *p) {
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                if at(function.entry, p[2]) < at(function.entry, p[1]) {
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                } else {
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                }
            } else {
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
            }
        } else {
            step();
            step();
            step();
            step();
            if at(function.entry, p[2]) < at(function.entry, p[1]) {
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                if at(function.entry, p[2]) < at(function.entry, *p) {
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                } else {
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                    step();
                }
            } else {
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
                step();
            }
        }
        unfold(sorted);
        unfold(sorted_range);
        have p[0] <= p[1] by simp;
        have p[1] <= p[2] by simp;
        have p[0] <= p[2] by {
            apply(int32_le_transitive(p[0], p[1], p[2]));
            assumption();
        }
    }
}
```

```expect
pass
```
