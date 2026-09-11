# A callback table initializer must match the field signature

The field's declared signature is the expected one, so an initializer naming a
function with a different C signature is rejected at the source boundary, with
the same diagnostic an assignment through a pointer produces.

```c filename=mismatched_callback_table.c
struct callbacks {
    int32 (*add)(int32, int32);
};

int32 negate(int32 value) {
    return 0 - value;
}

static const struct callbacks table = {
    .add = &negate
};

int32 caller() {
    return table.add(8, 3);
}
```

```click
verifying "mismatched_callback_table.c";
```

```expect
fail:callback signature mismatch: expected Int32 (Int32, Int32), got Int32 (Int32)
```
