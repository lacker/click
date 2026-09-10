# Integer witness must name the existential binder

```click
theorem integer_exists_witness_wrong_name(x: Integer) {
    ensures exists (z: Integer) { z == x } by {
        witness(y = x);
    }
}
```

```expect
fail: witness
```
