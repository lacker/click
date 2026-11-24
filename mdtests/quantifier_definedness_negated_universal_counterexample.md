# Quantifier definedness: negated universal counterexample

```click quick-solve
theorem check_quantifier() {
    ensures not (forall (k: int32) { to_uint8(to_integer(k)) != to_uint8(to_integer(k)) }) by { witness(0); close(); }
}
```

```expect
pass
```
