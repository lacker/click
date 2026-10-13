# Obtain bindings stay inside their subproof

```click
theorem scoped_witness(x: int32) {
    requires exists (k: int32) { k == x };
    ensures exists (z: int32) { z == x } by {
        have exists (a: int32) { a == x } by {
            obtain (k: int32) { k == x }
            have k == x by assumption();
            witness { a: k };
            assumption();
        }
        have k == x by assumption();
        witness { z: x };
        normalize();
    }
}
```

```expect
fail: unbound variable `k`
```
