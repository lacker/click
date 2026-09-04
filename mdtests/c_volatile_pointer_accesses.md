# pointer-derived volatile accesses retain execution evidence

The sequential volatile model carries the qualifier through a pointer to
scalar storage. It still does not model threads, atomics, signals, or device
state.

```c filename=c_volatile_pointer_accesses.c
int32 c_volatile_pointer_accesses() {
    int32 values[2] = {4, 6};
    volatile int32 *pointer = values;
    pointer[1] = pointer[0] + 1;
    return values[1];
}
```

```click
verifying "c_volatile_pointer_accesses.c";

int32 c_volatile_pointer_accesses() {
    ensures result == 5 by auto;
}
```

```expect
pass
```
