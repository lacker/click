# arithmetic rejects nonlinear expressions

```click
theorem nonlinear_product_is_outside_arithmetic(x: int32, y: int32) {
    requires x == 0;
    requires y == 0;

    ensures x * y == 0 by {
        arithmetic() using {
            x == 0;
            y == 0;
        }
    }
}
```

```expect
fail: atomic signed-affine int32 comparison goal
```
