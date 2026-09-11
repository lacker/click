# Writing a const callback table field is rejected

A callback field is an ordinary member of a `const` object: allowing the table
to be initialized must not make it writable.

```c filename=const_callback_table.c
struct callbacks {
    int32 (*add)(int32, int32);
};

int32 add(int32 left, int32 right) {
    return left + right;
}

int32 subtract(int32 left, int32 right) {
    return left - right;
}

static const struct callbacks table = {
    .add = &add
};

int32 bad() {
    table.add = &subtract;
    return table.add(8, 3);
}
```

```click
verifying "const_callback_table.c";
```

```expect
fail:cannot modify a const-qualified lvalue
```
