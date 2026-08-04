# a C recursion measure proves termination separately

The ordinary contract remains partial. `decreases` additionally asks the
kernel to check that every recursive edge lowers a nonnegative `int32`
parameter.

```c filename=c_decreases_recursive.c
int32 countdown(int32 n) {
    int32 result;
    if (n > 0) {
        result = countdown(n - 1);
        return result;
    }
    return 0;
}
```

```click
verifying "c_decreases_recursive.c";

int32 countdown(int32 n) {
    decreases n;
    ensures result == 0 by auto;
}
```

```expect
pass
```
