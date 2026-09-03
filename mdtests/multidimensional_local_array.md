# Multidimensional local arrays use row-major pointer arithmetic

The C0 frontend flattens scalar multidimensional arrays into the existing
stack block model. Indexing all dimensions computes the corresponding
row-major element offset before the kernel applies the element width.

```c filename=multidimensional_local_array.c
int32 matrix_value() {
    int32 values[2][3];
    values[1][2] = 7;
    return values[1][2];
}
```

```click
verifying "multidimensional_local_array.c";

int32 matrix_value() {
    ensures selected_cell: result == 7 by auto;
}
```

```expect
pass
```
