# Pointer arithmetic on a theorem parameter keeps its C meaning under Integer arithmetic

Under Integer specification arithmetic a comparison that does arithmetic compares exact
Integers, except where an arithmetic operand is a pointer. A theorem's pointer
parameter is such an operand, like a C function's: `base + offset` is pointer
arithmetic, so the comparison keeps its C meaning. The theorem is the one in the
owned-string example.

```click quick-solve

theorem pointer_add_zero_equals(
    base: int32*,
    offset: int32,
    target: int32*
) {
    requires base == target;
    requires offset == 0;

    ensures base + offset == target by {
        close();
    }
}
```

```expect
pass
```
