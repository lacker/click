# Integer existential witness in a pure theorem

```click quick-solve
theorem integer_exists_witness(x: Integer) {
    ensures exists (z: Integer) { z == x } by {
        witness(x);
        close();
    }
}
```

```expect
pass
```
