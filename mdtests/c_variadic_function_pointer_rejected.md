# Variadic function-pointer signatures are rejected

Only a function prototype may end in `...`; a callback signature may not.

```c filename=c_variadic_function_pointer_rejected.c
int32 run(int32 (*callback)(int32 code, ...), int32 value) {
    return value;
}
```

```click
verifying "c_variadic_function_pointer_rejected.c";

int32 run(int32 (*callback)(int32 code), int32 value) {
    ensures result == value by auto;
}
```

```expect
fail:c_variadic_function_pointer_rejected.c:1: variadic function-pointer signatures (`...`) are not supported by Click
```
