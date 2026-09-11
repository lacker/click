# Integer quantifiers retain independent C clauses

```click
theorem integer_quantifier_mixed(x: Integer, c: int32) {
    ensures forall (z: Integer) { z == z and c == c } by {
        intro();
        simp();
    }
}
```

```expect
pass
```
