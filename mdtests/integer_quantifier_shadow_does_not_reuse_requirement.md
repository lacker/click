# Integer binder shadowing does not reuse an outer requirement

```click
theorem integer_quantifier_shadow(z: Integer) {
    requires z == 0;
    ensures forall (z: Integer) { z == 0 } by {
        intro();
        assumption();
    }
}
```

```expect
fail: missing pure fact
```
