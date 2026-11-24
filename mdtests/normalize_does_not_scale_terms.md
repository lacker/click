# One symbolic distribution step

The distributivity identity holds with opaque operands. It requires no facts
about the individual operands.

```click quick-solve
theorem distributes_product(x: Integer, y: Integer, z: Integer) {
    ensures (x + y) * z == x * z + y * z by { close(); }
}
```

```expect
pass
```
