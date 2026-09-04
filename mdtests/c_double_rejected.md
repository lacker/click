# C0 rejects unsupported floating-point literal forms

```c filename=c_double_rejected.c
int32 c_double_rejected() {
    double value = 0x1.0p0;
    return 0;
}
```

```click
verifying "c_double_rejected.c";

int32 c_double_rejected() {
    ensures result == 0 by auto;
}
```

```expect
fail: hexadecimal floating-point literals are not supported in C0
```
