# a recursive termination measure cannot escape through a parameter address

The recursive call is guarded and decreases `n`, but the body writes through
`&n`. A termination measure whose address escapes is not stable enough to rank
the recursive edge.

```c filename=c_decreases_rejects_address_escaped_parameter.c
int32 escaped_parameter(int32 n) {
    int32* p;
    p = &n;
    if (n > 0) {
        *p = 1000;
        escaped_parameter(n - 1);
    }
    return 0;
}
```

```click
verifying "c_decreases_rejects_address_escaped_parameter.c";

int32 escaped_parameter(int32 n) {
    decreases n;
    ensures result == 0 by auto;
}
```

```expect
fail: termination measure `n` in `escaped_parameter` has its address taken
```
