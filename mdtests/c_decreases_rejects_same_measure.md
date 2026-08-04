# a recursive edge must strictly decrease

```c filename=c_decreases_rejects_same_measure.c
int32 stuck(int32 n) {
    int32 result;
    if (n > 0) {
        result = stuck(n);
        return result;
    }
    return 0;
}
```

```click
verifying "c_decreases_rejects_same_measure.c";

int32 stuck(int32 n) {
    decreases n;
    ensures result == 0 by auto;
}
```

```expect
fail: recursive call to `stuck` must pass `n - K`
```
