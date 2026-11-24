# Constructor injectivity needs the two constructors to be one value

`x` and `y` are unrelated, so `Full(a)` and `Full(b)` are in different
equality classes and nothing relates `a` to `b`. The positive is
[`constructor_injectivity_through_an_equal_value.md`](constructor_injectivity_through_an_equal_value.md).

```click quick-solve
spec enum Box { Full(int32), Empty }

theorem unrelated_values(x: Box, y: Box, a: int32, b: int32) {
    requires x == Box::Full(a);
    requires y == Box::Full(b);
    ensures a == b by close();
}
```

```expect
fail: `solve` failed
```
