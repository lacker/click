# Local array initializers lower to ordinary stores

The C initializer is preserved as source behavior: omitted elements are zero,
and the initialized array can be read through the normal array-indexing path.

```c filename=initialized_array.c
int32 initialized_array() {
    int32 values[3] = {4, 5};
    return values[2];
}
```

```click
verifying "initialized_array.c";

int32 initialized_array() {
    ensures omitted_element_is_zero: result == 0 by auto;
}
```

```expect
pass
```
