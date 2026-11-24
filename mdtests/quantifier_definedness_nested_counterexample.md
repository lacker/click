# Quantifier definedness: nested counterexample

```click quick-solve
theorem check_quantifier() {
    ensures forall (a: uint8) { not (forall (k: int32) { to_uint8(to_integer(k)) != to_uint8(to_integer(k)) }) } by { intro(); witness(0); close(); }
}
```

```expect
pass
```
