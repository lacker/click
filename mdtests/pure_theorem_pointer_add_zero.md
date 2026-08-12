# pure pointer-offset identity certificates

A pointer-arithmetic identity proved by smart `simp` must produce a pure
surface certificate: the int32 equality `offset == 0` rewrites inside the
pointer-offset goal, and the rewritten goal closes from the pointer equality
premise. The explicit spelling states the same certificate directly.

```click
theorem pointer_add_zero_equals(
    base: int32*,
    offset: int32,
    target: int32*
) {
    requires base == target;
    requires offset == 0;

    ensures base + offset == target by {
        simp();
    }
}

theorem pointer_add_zero_equals_explicit(
    base: int32*,
    offset: int32,
    target: int32*
) {
    requires base == target;
    requires offset == 0;

    ensures base + offset == target by {
        rewrite(offset == 0);
        assumption();
    }
}
```

```expect
pass
```
