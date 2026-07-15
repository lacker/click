# permission call returns write access

This checks the successful linear write-transfer shape. The helper receives
`write(p[0..1])` and returns the same write resource in its postcondition, so
the caller can prove it still has write permission after the call.

```c filename=write_and_return_permission.c
int32 write_and_return_permission(int32 p[]) {
    p[0] = 1;
    return p[0];
}
```

```c filename=call_write_and_keep_permission.c
int32 call_write_and_keep_permission(int32 p[]) {
    int32 value;
    value = write_and_return_permission(p);
    return value;
}
```

```click
verifying "write_and_return_permission.c";
verifying "call_write_and_keep_permission.c";

int32 write_and_return_permission(int32 p[]) {
    consumes p[0..1];

    ensures returns_written: result == p[0] by auto;
    produces p[0..1] by auto;
}

int32 call_write_and_keep_permission(int32 p[]) {
    consumes p[0..1];

    produces p[0..1] by auto;
}
```

```expect
pass
```
