# Machine quantifiers preserve the witness's width and signedness

```click
theorem wide_identity(n: int64) {
    ensures exists (x: int64) { x == n } by {
        witness { x: n };
        simp();
    }
}

theorem byte_identity(n: uint8) {
    ensures exists (x: uint8) { x == n } by {
        witness { x: n };
        simp();
    }
}
```

```expect
pass
```
