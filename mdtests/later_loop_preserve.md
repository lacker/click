# preservation proof at a later loop

Execution-proof traversal advances across the first loop with its abstract loop
rule before entering the preservation proof for the second loop.

```c filename=later_loop_preserve.c
int32 later_loop_preserve() {
    int32 i;
    int32 j;
    i = 0;
    while (i < 1) {
        i = i + 1;
    }
    j = 0;
    while (j < 1) {
        j = j + 1;
    }
    return i + j;
}
```

```click
verifying "later_loop_preserve.c";

int32 later_loop_preserve() {
    ensures result == 2;
} by {
    step();
    step();
    step();
    loop {
        invariant i >= 0 and i <= 1;
    }
    step();
    loop {
        invariant j >= 0 and j <= 1;
        preserve by {
            step();
            simp();
        }
    }
    have i == 1 by simp;
    have j == 1 by simp;
    step();
    simp();
}
```

```expect
pass
```
