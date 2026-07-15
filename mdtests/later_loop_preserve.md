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
    for loop(0) {
        invariant i >= 0 and i <= 1;
    }
    for loop(1) {
        invariant j >= 0 and j <= 1;
        preserve by {
            execute_step();
            simp();
        }
    }
    ensures result == 2 by auto;
}
```

```expect
pass
```
