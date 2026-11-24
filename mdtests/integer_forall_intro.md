# Integer universal introduction and specialization

```click quick-solve
theorem integer_forall_intro(x: Integer) {
    ensures forall (z: Integer) { z + x == x + z } by {
        intro();
        close();
    }
}
```

```expect
pass
```
