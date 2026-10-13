# Click rejects variadic function definitions

Only a body-less variadic prototype is retained. A definition would read its
variable arguments through `va_arg`, which Click does not model.

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
fail:c_variadic_rejected.c:1: variadic function definitions (`...`) are not supported by Click; only a body-less prototype of `c_variadic_rejected` can be declared
```
