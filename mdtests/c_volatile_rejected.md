# C0 rejects volatile declarations

```c filename=c_volatile_rejected.c
int32 c_volatile_rejected() {
    volatile int32 value;
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
fail: the `volatile` qualifier is not supported in C0
```
