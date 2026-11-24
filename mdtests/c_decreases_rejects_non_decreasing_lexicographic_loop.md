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
        initialize by close();
        maintain by {
            if j > 0 {
                step();
                step();
                close();
            } else {
                have 0 <= to_integer(i - 1);
                step();
                step();
                step();
                have i >= 0 by { close() using { 0 <= i; }; }
                close();
            }
        }
    }
    step();
    close();
}
```

```expect
fail: `(i, j)` decreases at the back edge
```
