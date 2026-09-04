# C0 rejects unsupported volatile pointer depth

```c filename=c_volatile_rejected.c
int32 c_volatile_rejected() {
    volatile int32 **pointer;
    return 0;
}
```

```click
verifying "c_volatile_rejected.c";

int32 c_volatile_rejected() {
    ensures result == 0 by auto;
}
```

```expect
fail: supports scalar objects and pointers to scalar objects
```
