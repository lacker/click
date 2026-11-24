# `defined` of a conversion claims its range with its operand as a value

Guarded by `defined(a / b)`, `defined(to_int32(to_integer(a / b) + 1))` reads
the Integer sum as a value and claims that it fits in `int32`.

```click quick-solve
theorem integer_operand_given(a: int32, b: int32) {
    requires defined(a / b) and defined(to_int32(to_integer(a / b) + 1));
    ensures to_integer(a / b) + 1 <= 2147483647 by close();
}
```

```expect
pass
```
