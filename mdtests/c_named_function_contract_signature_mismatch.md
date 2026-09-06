# Named contracts check function-pointer signatures

A contract application is typed at the use site. Matching a function name or
an ABI pointer shape is not enough when the callback has the wrong parameter
list.

```c filename=unary_apply.c
int32 unary_apply(int32 (*callback)(int32), int32 value) {
    int32 result;
    result = callback(value);
    return result;
}
```

```click
verifying "unary_apply.c";

contract int32 Binary(int32 left, int32 right) {
    ensures result == left + right;
}

int32 unary_apply(int32 (*callback)(int32), int32 value) {
    requires Binary(callback);
}
```

```expect
fail: contract `Binary` expects
```
