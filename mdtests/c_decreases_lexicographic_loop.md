# a loop measure can use lexicographic phases

```c filename=c_decreases_lexicographic_loop.c
int32 phase_count(int32 n) {
    int32 i;
    int32 j;
    i = n;
    j = 2;
    while (i > 0) {
        if (j > 0) {
            j = j - 1;
        } else {
            i = i - 1;
            j = 2;
        }
    }
    return i;
}
```

```click
verifying "c_decreases_lexicographic_loop.c";

int32 phase_count(int32 n) {
    requires n >= 0;
    ensures result == 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases (i, j);
        invariant i >= 0;
        invariant j >= 0;
        invariant j <= 2;
        initialize by simp;
        preserve by {
            if j > 0 {
                have 0 <= j - 1 by {
                    apply(int32_positive_predecessor_is_nonnegative(j)) using { j > 0; }
                }
                step();
                step();
                have j >= 0 by { arithmetic() using { 0 <= j; } }
                simp();
            } else {
                have 0 <= i - 1 by {
                    apply(int32_positive_predecessor_is_nonnegative(i)) using { i > 0; }
                }
                step();
                step();
                step();
                have i >= 0 by { arithmetic() using { 0 <= i; } }
                simp();
            }
        }
    }
    step();
    simp();
}
```

```expect
pass
```
