# `loop diverges` needs the function to say so too

A loop that may never exit is a function that may never return, so the marker
belongs on the signature as well as on the loop head.

```c filename=diverges_loop_requires_marked_function.c
int32 wait_for_zero(int32 x) {
    while (x != 0) {
    }
    return 1;
}
```

```click
verifying "diverges_loop_requires_marked_function.c";

int32 wait_for_zero(int32 x) {
    ensures result == 1;
} by {
    loop diverges {
        invariant x == x;
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
fail: the loop in `wait_for_zero` is declared `diverges`, so `wait_for_zero` must be declared `diverges` too
```
