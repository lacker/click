# solve refuses a bound one below its chain

`x < n` and `n <= 4` give `x <= 3`, not `x <= 2`.

```click quick-solve
theorem too_tight(x: int32, n: int32) {
    requires x < n;
    requires n <= 4;
    ensures x <= 2 by close();
}
```

```expect
fail: could not establish `x <= 2`
```
