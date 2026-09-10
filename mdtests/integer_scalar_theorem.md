# mathematical Integer scalar theorem

This checks theorem parameters and exact mathematical scalar comparisons.

```click
theorem integer_scalar_theorem(x: Integer) {
    let z: Integer = -1;
    ensures z + (1 + 2) == z + 3 by {
        simp();
    }
}
```

```expect
pass
```
