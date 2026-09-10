# Integer binder shadowing does not reuse an outer requirement

```click
theorem integer_quantifier_shadow(z: Integer) {
    requires z == 0;
    ensures forall (z: Integer) { z == 0 } by {
        intro();
        have z == 0 by { assumption(); }
        assumption();
    }
}
```

```expect
fail: could not lower `have` proposition
```
