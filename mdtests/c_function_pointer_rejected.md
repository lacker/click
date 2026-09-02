# C0 rejects function-pointer declarations

```c filename=c_function_pointer_rejected.c
int32 c_function_pointer_rejected() {
    int32 (*callback)(int32);
    return 0;
}
```

```click
verifying "c_function_pointer_rejected.c";

int32 c_function_pointer_rejected() {
    ensures result == 0 by auto;
}
```

```expect
fail: function-pointer declarations are not supported in C0
```
