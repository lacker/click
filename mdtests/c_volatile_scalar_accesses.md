# scalar volatile accesses retain execution evidence

The first volatile model keeps direct scalar accesses in the checked
execution trace. It does not attempt to model threads, atomics, signals, or
external device state.

```c filename=c_volatile_scalar_accesses.c
int32 c_volatile_scalar_accesses() {
    volatile int32 value = 4;
    value = value + 1;
    return value;
}
```

```click
verifying "c_volatile_scalar_accesses.c";

int32 c_volatile_scalar_accesses() {
    ensures result == 5 by auto;
}
```

```expect
pass
```
