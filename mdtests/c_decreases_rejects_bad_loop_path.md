# every loop back edge must decrease

```c filename=c_decreases_rejects_bad_loop_path.c
int32 sometimes_stuck(int32 n, int32 choose) {
    while (n > 0) {
        if (choose == 0) {
            n = n - 1;
        }
    }
    return n;
}
```

```click
verifying "c_decreases_rejects_bad_loop_path.c";

int32 sometimes_stuck(int32 n, int32 choose) {
    requires n >= 0;
    for loop(0) {
        decreases n;
        invariant n >= 0;
    }
    ensures result == 0 by auto;
}
```

```expect
fail: does not decrease `n` to a nonnegative value on every back edge
```
