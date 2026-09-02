# C0 rejects floating-point declarations

```c filename=c_double_rejected.c
int32 c_double_rejected() {
    double value;
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
fail: unsupported C type `double`: floating-point values are not modeled in C0
```
