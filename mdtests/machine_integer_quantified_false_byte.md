# machine integer quantified false byte

```click
theorem bad(n: uint8) {
    ensures exists (x: uint8) { x + 1 == n } by {
        witness { x: n };
        normalize();
    }
}
```

```expect
fail: did not normalize to true
```
