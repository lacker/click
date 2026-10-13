# `auto` proves a signed addition defined from its `Integer` bounds

`defined(a + b)` over `int32` or `int64` holds when the exact sum is in the
type's range. `auto` proves both bounds with the solver and applies
`int32_add_defined_by_integer_bounds` (or the `int64` one).

```click
theorem addition_defined(total: int32, b: int32) {
    requires 0 <= total;
    requires total <= 255000;
    requires 0 <= b;
    requires b <= 255;
    ensures defined(total + b) by {
        have defined(total + b) by auto;
        assumption();
    }
}
```

```expect
pass
```
