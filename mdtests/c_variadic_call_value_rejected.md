# A variadic call is rejected in value position too

```c filename=c_variadic_call_value_rejected.c
int report(int code, ...);

int32 run(int32 value) {
    int32 status = report(value, 1);
    return status;
}
```

```click
verifying "c_variadic_call_value_rejected.c";

int32 run(int32 value) {
    ensures true by auto;
}
```

```expect
fail:c_variadic_call_value_rejected.c:4: calls to variadic function `report` are not supported by Click
```
