# a recursive call in a loop still needs a strict function-level descent

The loop is finite, but that does not make the recursive edge safe. Passing
the unchanged `n` must still be rejected.

```c filename=c_decreases_recursive_in_loop_rejects_same_measure.c
int32 stuck_loop(int32 n) {
    int32 i;
    int32 result;
    i = 0;
    result = 0;
    while (i < 1) {
        if (n > 0) {
            result = stuck_loop(n);
        } else {
            result = 0;
        }
        i++;
    }
    return result;
}
```

```click
verifying "c_decreases_recursive_in_loop_rejects_same_measure.c";

int32 stuck_loop(int32 n) {
    decreases n;
    ensures result == 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases 1 - i;
        invariant i >= 0;
        invariant i <= 1;
        invariant result == 0;
        initialize by simp;
        preserve by {
            if n > 0 {
                step();
                step();
                simp();
            } else {
                step();
                step();
                simp();
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
fail: recursive call to `stuck_loop` must pass `n - K`
```
