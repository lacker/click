# machine integer quantified range stays scoped

```click quick-solve
theorem bad(n: int32) {
    requires forall (x: uint8) { x <= 255 };
    ensures n <= 255 by close();
}
```

```expect
fail: could not establish
```
