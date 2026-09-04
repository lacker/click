# a recursive termination parameter cannot be changed by an update

The `n++` update happens before the recursive edge, so the apparent `n - 1`
argument is not a decrease from the function's entry measure.

```c filename=c_decreases_rejects_updated_parameter.c
int32 updated_parameter(int32 n) {
    n++;
    if (n > 0) {
        updated_parameter(n - 1);
    }
    return 0;
}
```

```click
verifying "c_decreases_rejects_updated_parameter.c";

int32 updated_parameter(int32 n) {
    decreases n;
    requires n < 2147483647;
    ensures result == 0 by auto;
}
```

```expect
fail: termination measure `n` is reassigned
```
