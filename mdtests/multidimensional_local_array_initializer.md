# Multidimensional scalar arrays accept nested initializers

Nested C initializers are flattened in row-major order into the existing local
array block. Omitted cells remain explicitly zero-initialized, as in C.

```c filename=multidimensional_local_array_initializer.c
int32 multidimensional_local_array_initializer() {
    int32 values[2][3] = {{1, 2, 3}, {4, 5, 6}};
    return values[1][2];
}
```

```click
verifying "multidimensional_local_array_initializer.c";

int32 multidimensional_local_array_initializer() {
    ensures result == 6 by auto;
}
```

```expect
pass
```
