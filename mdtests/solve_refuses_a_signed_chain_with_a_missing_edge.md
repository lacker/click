# solve refuses a signed chain with a missing edge

Nothing relates `a` to `b`, so `x < a` and `b <= 4` do not give `x < 4`.

```click quick-solve
theorem broken(x: int32, a: int32, b: int32) {
    requires x < a;
    requires b <= 4;
    ensures x < 4 by close();
}
```

```expect
fail: could not establish `x < 4`
```
