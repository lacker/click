# a function is ranked or divergent, never both

A function-level `decreases` asks Click to certify that the function returns.
A `diverges` signature says it may not, so the two cannot be written together.

```c filename=diverges_function_rejects_decreases.c
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
verifying "diverges_function_rejects_decreases.c";

int32 countdown(int32 n) diverges {
    decreases n;
    requires n >= 0;
    ensures result == 0;
}
```

```expect
fail: `countdown` is declared `diverges` and cannot also carry a function-level `decreases` clause
```
