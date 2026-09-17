# a loop is ranked or divergent, never both

A `decreases` clause claims the loop exits and a `diverges` head claims it may
not, so one loop cannot carry both.

```c filename=diverges_loop_rejects_decreases.c
int32 drain(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
    return n;
}
```

```click
verifying "diverges_loop_rejects_decreases.c";

int32 drain(int32 n) diverges {
    requires n >= 0;
    ensures result == 0;
} by {
    loop diverges {
        decreases n;
        invariant n >= 0;
        initialize by simp;
        preserve by {
            step();
            close_invariants by { simp(); }
        }
    }
    step();
    simp();
}
```

```expect
fail: the loop is declared `diverges` and cannot also carry a `decreases` clause
```
