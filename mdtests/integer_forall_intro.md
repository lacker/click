# Integer universal introduction and specialization

```click
theorem integer_forall_intro(x: Integer) {
    ensures forall (z: Integer) { z + x == x + z } by {
        intro();
        simp();
    }
}
```

```expect
pass
```
