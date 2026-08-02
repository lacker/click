# bubble_pass3 moves the maximum to the end

This checks the first loop-invariant sorting step: one bubble-sort pass over
three cells should establish that every earlier cell is less than or equal to
the final cell. It intentionally does not prove permutation.

```c filename=bubble_pass3.c
int32 bubble_pass3(int32 p[3]) {
    int32 j;
    int32 tmp;
    j = 0;
    while (j < 2) {
        if (p[j + 1] < p[j]) {
            tmp = p[j];
            p[j] = p[j + 1];
            p[j + 1] = tmp;
        }
        j = j + 1;
    }
    return 0;
}
```

```click
verifying "bubble_pass3.c";

predicate all_le_range(p: int32[], lo: int32, hi: int32, x: int32) {
    forall (k: int32) {
        0 <= k and lo <= k and k < hi implies p[k] <= x
    }
}

int32 bubble_pass3(int32 p[3]) {
    requires loadable(p[0..3]);
    consumes p[0..3];
    for loop(0) {
        invariant j >= 0 and j <= 2;
        invariant all_le_range(p, 0, j, p[j]);
        initialize by {
            unfold(all_le_range);
            simp();
        }
        preserve by {
            unfold(all_le_range);
        }
        mutable p[0..3] by frame;
    }
    ensures max_at_end: all_le_range(p, 0, 2, p[2]) by {
        execute();
        unfold(all_le_range);
        simp();
    }
}
```

```expect
pass
```
