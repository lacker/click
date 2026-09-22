# Boolean integer promotion preserves division by zero

```c filename=boolean_divide.c
int divide_by_false(void) {
    _Bool b = 0;
    return 1 / b;
}
```

```click
verifying "boolean_divide.c";
int32 divide_by_false() { ensures result == 0; } by { execute(); simp(); }
```

```expect
fail: undefined behavior: division by zero
```
