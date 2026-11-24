# Constructor injectivity joins only matching field positions

`x` equals two `Pair` constructors, so `a == c` and `b == d`. Nothing relates
`a` to `d`. The positive is
[`constructor_injectivity_through_an_equal_value.md`](constructor_injectivity_through_an_equal_value.md).

```click quick-solve
spec enum Pair { Pair(int32, int32) }

theorem crossed_fields(x: Pair, a: int32, b: int32, c: int32, d: int32) {
    requires x == Pair::Pair(a, b);
    requires x == Pair::Pair(c, d);
    ensures a == d by close();
}
```

```expect
fail: `solve` failed
```
