# a lexicographic loop measure must decrease on every back edge

```c filename=c_decreases_rejects_non_decreasing_lexicographic_loop.c
int32 stuck_phase(int32 n) {
    int32 i;
    int32 j;
    i = n;
    j = 2;
    while (i > 0) {
        if (j > 0) {
            j = j;
        } else {
            i = i - 1;
            j = 2;
        }
    }
    return i;
}
```

```click
verifying "c_decreases_rejects_non_decreasing_lexicographic_loop.c";

int32 stuck_phase(int32 n) {
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
                step();
                step();
                simp();
            } else {
                step();
                step();
                step();
                simp();
            }
        }
    }
    step();
    simp();
}
```

```expect
fail: loop 0 does not decrease `(i, j)`
```
