# nested loops can be ranked as terminating phases

The outer loop's first ranking component decreases after an inner loop has
finished. The inner loop changes the outer tuple's second component, so the
outer checker must forget that value rather than assume the inner loop's
exact final state.

```c filename=c_decreases_nested_loop.c
int32 nested_count(int32 n, int32 m) {
    int32 i;
    int32 j;
    i = n;
    j = 0;
    while (i > 0) {
        j = 0;
        while (j < m) {
            j++;
        }
        i--;
    }
    return i;
}
```

```click
verifying "c_decreases_nested_loop.c";

int32 nested_count(int32 n, int32 m) {
    requires n >= 0 and m >= 0;
    ensures result == 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases (i, m - j);
        invariant i >= 0;
        invariant j >= 0;
        invariant j <= m;
        initialize by simp;
        preserve by {
            step();
            loop {
                decreases m - j;
                invariant j >= 0;
                invariant j <= m;
                initialize by simp;
                preserve by {
                    step();
                    close_invariants();
                }
            }
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
