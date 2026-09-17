# A contract struct cast names a declared struct

```c filename=unknown_cast.c
int pick(void *argument) {
    return 0;
}
```

```click
verifying "unknown_cast.c";

int32 pick(void *argument) {
    requires ((struct missing *)argument) != 0;
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
fail: unknown struct declaration `missing` in pointer cast
```
