# external function calls require their declared preconditions

```c filename=caller.c
int32 caller() {
    int32 result;
    result = external_identity(-1);
    return result;
}
```

```click
verifying "caller.c";

extern int32 external_identity(int32 x) {
    requires x >= 0;
    ensures result == x;
}

int32 caller() {
    ensures result == -1;
}
```

```expect
fail: external_identity precondition
```
