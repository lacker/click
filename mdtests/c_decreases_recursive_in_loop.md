# recursive calls inside a ranked loop use both termination arguments

The loop and the recursive call have independent finite measures. The loop
executes once, while the recursive edge is taken only on the positive-
`n` path and receives `n - 1`.

```c filename=c_decreases_recursive_in_loop.c
int32 recursive_loop(int32 n) {
    int32 i;
    int32 result;
    i = 0;
    result = 0;
    while (i < 1) {
        if (n > 0) {
            result = recursive_loop(n - 1);
        } else {
            result = 0;
        }
        i++;
    }
    return result;
}
```

```click
verifying "c_decreases_recursive_in_loop.c";

int32 recursive_loop(int32 n) {
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
pass
```
