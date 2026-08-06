# bubble_sort3_two_pass proves sortedness with loop invariants

This checks that a fixed-size two-pass bubble sort over three cells can prove
sortedness from loop VCs and quantified invariants, without bounded execution.

```c filename=bubble_sort3_two_pass.c
int32 bubble_sort3_two_pass(int32 p[3]) {
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
    j = 0;
    while (j < 1) {
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
verifying "bubble_sort3_two_pass.c";

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

predicate all_le_range(p: int32[], lo: int32, hi: int32, x: int32) {
    forall (k: int32) {
        0 <= k and lo <= k and k < hi implies p[k] <= x
    }
}

int32 bubble_sort3_two_pass(int32 p[3]) {
    requires loadable(p[0..3]);
    consumes p[0..3];
    ensures sorted: sorted(p, 3);
} by {
    step();
    step();
    step();
    loop {
        invariant j >= 0 and j <= 2;
        invariant all_le_range(p, 0, j, p[j]);
        initialize by {
            unfold(all_le_range);
            simp();
        }
        preserve by {
            unfold(all_le_range);
        }
    }
    step();
    loop {
        invariant j >= 0 and j <= 1;
        invariant all_le_range(p, 0, 2, p[2]);
        invariant all_le_range(p, 0, j, p[j]);
        initialize by {
            unfold(all_le_range);
            simp();
        }
        preserve by {
            unfold(all_le_range);
        }
    }
    step();
    unfold(sorted);
    unfold(sorted_range);
    unfold(all_le_range);
    simp();
}
```

```expect
pass
```
