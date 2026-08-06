# preservation proof at a nested loop

The inner loop proof starts from an arbitrary outer-loop iteration and the
state obtained by advancing through the outer body prefix.

```c filename=nested_loop_preserve.c
int32 nested_loop_preserve() {
    int32 i;
    int32 j;
    i = 0;
    while (i < 1) {
        j = 0;
        while (j < 1) {
            j = j + 1;
        }
        i = i + 1;
    }
    return i;
}
```

```click
verifying "nested_loop_preserve.c";

int32 nested_loop_preserve() {
    ensures result == 1;
} by {
    step();
    step();
    step();
    loop {
        invariant i >= 0 and i <= 1;
        preserve by {
            step();
            loop {
                invariant j >= 0 and j <= 1;
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
