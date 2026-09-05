# Opaque object pointers do not change function-pointer signatures

```c filename=c_void_pointer_callback_rejected.c
int32 typed_compare(int32 *left, int32 *right) {
    return left == right;
}

int32 apply(int32 (*compare)(const void *, const void *),
            const void *left, const void *right) {
    return compare(left, right);
}

int32 caller(int32 *value) {
    return apply(&typed_compare, value, value);
}
```

```click
verifying "c_void_pointer_callback_rejected.c";

int32 typed_compare(int32 *left, int32 *right) {
    requires left == right;
    ensures result == 1 by auto;
}

int32 apply(int32 (*compare)(const void *, const void *),
            const void *left, const void *right) {
    ensures result == 1 by auto;
}

int32 caller(int32 *value) {
    ensures result == 1;
}
```

```expect
fail: no compatible target for function pointer
```
