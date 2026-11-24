# Loop invariants explain the supported entry state

```c filename=r.c
int count(void) {
    int i = 0;
    while (i < 3) {
        int j = 0;
        while (j < 2) {
            j = j + 1;
        }
        i = i + 1;
    }
    return i;
}
```

```click
verifying "r.c";
int32 count() {
    ensures result == result;
} by {
    step_until(loop(0).entry);
    loop {
        decreases 3 - i;
        invariant i <= 3;
        maintain by {
            mark outer_head;
            have at(outer_head, i) < 3 by { close(); }
            step_until(loop(1).entry);
            loop {
                decreases 2 - j;
                invariant j <= 2;
                invariant at(outer_head, i) < 3;
                maintain by {
                    have at(outer_head, i) < 3 by { close(); }
                    step_until(loop.back_edge);
                }
            }
            step_until(loop.back_edge);
        }
    }
}
```

```expect
fail: use `at(loop(1).entry, ...)`
```
