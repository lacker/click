# dynamic static integer initializers remain rejected

Static storage can fold bounded integer constant expressions, but it must not
silently turn a runtime load into an initialization-time value.

```c filename=dynamic_static_integer_initializer.c
int32 seed = 1;
int32 value = seed + 1;

int32 read_value() {
    return value;
}
```

```click
verifying "dynamic_static_integer_initializer.c";
```

```expect
fail: integer constant expressions
```
