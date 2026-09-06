# static integer initializers fold bounded constant expressions

Integer initializers for file-scope globals, file-scope `static` objects,
function-local `static` objects, and scalar arrays may use bounded arithmetic,
bitwise, and shift expressions. The parser folds them to literals before the
stable static-storage model is built.

```c filename=static_integer_constant_initializers.c
int32 values[3] = {
    1 + 2,
    (1 << 3) | 1,
    20 / 4
};

static int32 private_value = (6 << 1) ^ 3;

int32 read_values() {
    static int32 local_value = (8 >> 1) ^ 3;
    return values[0] + values[1] + values[2]
        + private_value + local_value;
}
```

```click
verifying "static_integer_constant_initializers.c";

int32 read_values() {
    ensures result == 39 by auto;
}
```

```expect
pass
```
