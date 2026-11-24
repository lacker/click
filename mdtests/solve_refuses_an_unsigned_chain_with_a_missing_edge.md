# solve refuses an unsigned chain with a missing edge

Nothing relates `a` to `b`, so `x < a` and `b <= 4u32` do not give `x < 4u32`.

```click quick-solve
theorem broken(x: uint32, a: uint32, b: uint32) {
    requires x < a;
    requires b <= 4u32;
    ensures x < 4u32 by close();
}
```

```expect
fail: could not establish `x < 4u32`
```
