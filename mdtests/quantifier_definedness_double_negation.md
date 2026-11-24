# Quantifier definedness: double negation

```click quick-solve
theorem check_quantifier() {
    ensures not (not (exists (k: int32) { to_uint8(to_integer(k)) == to_uint8(to_integer(k)) })) by { witness(0); close(); }
}
```

```expect
pass
```
