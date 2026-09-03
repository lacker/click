# an external declaration needs a contract

```c filename=caller.c
int32 caller(int32 x) {
    int32 result;
    result = external_identity(x);
    return result;
}
```

```click
verifying "caller.c";

extern int32 external_identity(int32 x) {}

int32 caller(int32 x) {
    ensures result == x;
}
```

```expect
fail: must contain at least one `ensures`
```
