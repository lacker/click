# Integer existential witness in a pure theorem

```click
theorem integer_exists_witness(x: Integer) {
    ensures exists (z: Integer) { z == x } by {
        witness(z = x);
        simp();
    }
}
```

```expect
pass
```
