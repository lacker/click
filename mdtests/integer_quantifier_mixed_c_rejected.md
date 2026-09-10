# Integer quantifiers reject mixed C clauses in the pure Integer intro path

```click
theorem integer_quantifier_mixed(x: Integer, c: int32) {
    ensures forall (z: Integer) { z == z and c == c } by {
        intro();
        simp();
    }
}
```

```expect
fail: `intro` requires
```
