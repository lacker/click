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
        } else {
            p[j] = p[j];
        }
        j = j + 1;
    }
    j = 0;
    while (j < 1) {
        if (p[j + 1] < p[j]) {
            tmp = p[j];
            p[j] = p[j + 1];
            p[j + 1] = tmp;
        } else {
            p[j] = p[j];
        }
        j = j + 1;
    }
    return 0;
}
```

```click
verifying "bubble_sort3_two_pass.c";

predicate sorted(int32 p[], int32 n) {
    sorted_range(p, 0, n)
}

predicate sorted_range(int32 p[], int32 lo, int32 hi) {
    forall (int32 i) {
        forall (int32 j) {
            0 <= i and 0 <= j and lo <= i and i < j and j < hi implies p[i] <= p[j]
        }
    }
}

predicate all_le_range(int32 p[], int32 lo, int32 hi, int32 x) {
    forall (int32 k) {
        0 <= k and lo <= k and k < hi implies p[k] <= x
    }
}

int32 bubble_sort3_two_pass(int32 p[3]) {
    requires loadable(p[0..3]);
    requires write(p[0..3]);
    for loop(0) {
        invariant j >= 0 and j <= 2;
        invariant all_le_range(p, 0, j, p[j]);
        initialize by {
            unfold(all_le_range);
        }
        preserve by {
            unfold(all_le_range);
        }
    }
    for loop(1) {
        invariant j >= 0 and j <= 1;
        invariant all_le_range(p, 0, 2, p[2]);
        invariant all_le_range(p, 0, j, p[j]);
        initialize by {
            unfold(all_le_range);
        }
        preserve by {
            unfold(all_le_range);
        }
    }
    ensures sorted: sorted(p, 3) by {
        symbolic_execute();
        loop_vc(loop(0));
        loop_vc(loop(1));
        unfold(sorted);
        unfold(sorted_range);
        unfold(all_le_range);
        simp();
    }
}
```

```expect
pass
```
