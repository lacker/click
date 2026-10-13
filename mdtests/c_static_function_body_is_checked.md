# A `static` function's body decides what its callers compute

The caller's claim is checked against the static function's actual body, not
against an assumed contract.

```c filename=c_static_function_body_is_checked.c
static int add_one(int value) {
    return value + 2;
}

int32 run(int32 value) {
    return add_one(value);
}
```

```click
verifying "c_static_function_body_is_checked.c";

int32 run(int32 value) {
    requires value < 100;
    ensures result == value + 1 by auto;
}
```

```expect
fail: left side evaluated to value + 2, right side evaluated to value + 1
```
