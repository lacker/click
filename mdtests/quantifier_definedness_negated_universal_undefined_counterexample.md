# Quantifier definedness: negated universal undefined counterexample

```click
theorem check_quantifier() {
    ensures not (forall (k: int32) { to_uint8(to_integer(k)) != to_uint8(to_integer(k)) }) by { witness(-1); close(); }
}
```

```expect
fail: solve
```
