# machine integer quantified wrong width

```click
theorem bad(n: int32) {
    ensures exists (x: int64) { x == x } by {
        witness { x: n };
        simp();
    }
}
```

```expect
fail: wrong type: expected int64, got int32
```
