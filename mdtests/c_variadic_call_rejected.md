# Calls to a variadic function are rejected

The prototype is retained, but its variable arguments have no model. A call
is refused at its own line even when the sidecar supplies an `extern`
contract for the named parameters and the call passes no variable arguments.

```c filename=c_variadic_call_rejected.c
int report(int code, ...);

int32 run(int32 value) {
    report(value);
    return value;
}
```

```click
verifying "c_variadic_call_rejected.c";

extern int32 report(int32 code) {
    ensures result == code;
}

int32 run(int32 value) {
    ensures result == value by auto;
}
```

```expect
fail:c_variadic_call_rejected.c:4: calls to variadic function `report` are not supported by Click; its variable arguments are not modeled
```
