# C0 rejects unsupported volatile aliases

```c filename=c_volatile_rejected.c
int32 c_volatile_rejected() {
    volatile int32 value;
    int32 *pointer = &value;
    return *pointer;
}
```

```click
verifying "c_volatile_rejected.c";

int32 c_volatile_rejected() {
    ensures result == 0 by auto;
}
```

```expect
fail: taking a volatile object's address
```
