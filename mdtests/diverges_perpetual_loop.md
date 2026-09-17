# a declared `diverges` loop may never exit

The loop exits only when `x` is already zero, so the function may run forever.
The signature says so with `diverges`, and the loop head says which loop is
the one that may not exit. This is today's partial correctness, named out
loud: the `ensures` still holds if the function returns.

```c filename=diverges_perpetual_loop.c
int32 wait_for_zero(int32 x) {
    while (x != 0) {
    }
    return 1;
}
```

```click
verifying "diverges_perpetual_loop.c";

int32 wait_for_zero(int32 x) diverges {
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
pass
```
