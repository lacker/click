# recursive contracts do not hide finite undefined behavior

The recursive hypothesis is partial-correctness reasoning, not an assumption
that the body is safe. Click must still reject an unsafe finite prefix.

```c filename=bad_recursive.c
int32 bad_recursive(int32 n) {
    int32 zero;
    int32 result;
    zero = 0;
    result = n / zero;
    result = bad_recursive(result);
    return result;
}
```

```click
verifying "bad_recursive.c";

int32 bad_recursive(int32 n) {
    ensures result == result by auto;
}
```

```expect
fail: division by zero
```
