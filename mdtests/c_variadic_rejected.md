# C0 rejects variadic parameter lists

```c filename=c_variadic_rejected.c
int32 c_variadic_rejected(int32 first, ...) {
    return first;
}
```

```click
verifying "c_variadic_rejected.c";

int32 c_variadic_rejected(int32 first) {
    ensures result == first by auto;
}
```

```expect
fail: variadic parameter lists (`...`) are not supported in C0
```
