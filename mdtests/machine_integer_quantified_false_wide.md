# machine integer quantified false wide

```click
theorem bad(n: int64) {
    requires 0i64 <= n and n <= 100i64;
    ensures exists (x: int64) { x == n + 1i64 } by {
        witness { x: n };
        normalize();
    }
}
```

```expect
fail: did not normalize to true
```
