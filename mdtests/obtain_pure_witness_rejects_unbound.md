# Obtain does not bind unrelated names

```click
theorem unrelated_name(x: int32) {
    requires exists (k: int32) { k == x };
    ensures exists (z: int32) { z == x } by {
        obtain (k: int32) { k == x }
        have missing == x by assumption();
        witness { z: k };
        assumption();
    }
}
```

```expect
fail: unbound variable `missing`
```
