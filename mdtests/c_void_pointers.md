# Opaque object pointers preserve identity across compatible views

`void *` and `const void *` carry an object pointer's identity without
inventing an element width. They can be compared and converted back to a
modeled typed pointer. Abstract calls through a generic callback require the
separately tracked higher-order function-contract feature.

```c filename=c_void_pointers.c
int32 compare_keys(const void *left, const void *right) {
    return left == right;
}

void *erase_type(int32 *value) {
    return value;
}

int32 *restore_type(void *value) {
    return (int32 *)value;
}

int32 round_trip(int32 *value) {
    void *opaque;
    int32 *restored;
    opaque = erase_type(value);
    restored = restore_type(opaque);
    return restored == value;
}

int32 null_key(const void *key) {
    return key == 0;
}
```

```click
verifying "c_void_pointers.c";

int32 compare_keys(const void *left, const void *right) {
    requires left == right;
    ensures result == 1 by auto;
}

void *erase_type(int32 *value) {
    ensures result == value by auto;
}

int32 *restore_type(void *value) {
    ensures result == value by auto;
}

int32 round_trip(int32 *value) {
    ensures result == 1 by auto;
}

int32 null_key(const void *key) {
    requires key == 0;
    ensures result == 1 by auto;
}
```

```expect
pass
```
