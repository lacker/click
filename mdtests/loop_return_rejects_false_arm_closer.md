# A false return-arm closer is rejected

The contract is true, but the written returning arm claims the wrong result.
Verification must check that arm instead of substituting the tail.

```c filename=loop_return_rejects_false_arm_closer.c
int32 f(int32 n) {
    int32 i = 0;
    while (i < n) {
        if (i == 2) {
            return 7;
        }
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_return_rejects_false_arm_closer.c";

int32 f(int32 n) {
    requires n == 5;
    ensures result == 5 or result == 7;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;
        maintain by {
            if i == 2 {
                step();
                step();
                have result == 5 by close();
                close();
            } else {
                step();
                step();
                step();
            }
        }
    }
    step();
    have result == 5 by close();
    close();
}
```

```expect
fail: could not establish `result == 5`
```
