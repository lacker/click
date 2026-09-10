# Arithmetic-free Integer witness goals outside the current pure fragment are rejected

```click
theorem integer_exists_witness_false(x: Integer) {
    ensures exists (z: Integer) { z == 0 } by {
        witness(z = x);
        simp();
    }
}
```

```expect
fail: `witness` is not available in a pure proof
```
