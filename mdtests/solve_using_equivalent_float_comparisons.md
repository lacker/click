# Mirrored float comparisons keep IEEE semantics

```click quick-solve
function fixed_float(x: double) -> double {
    float64_from_bits(0x3ff0000000000000)
}

theorem positive_float(x: double) {
    ensures fixed_float(x) > float64_from_bits(0) by {
        unfold(fixed_float(x)); close();
    }
}

theorem test(value: double) {
    ensures float64_from_bits(0) < fixed_float(value) by { close() using {}; }
    ensures float64_from_bits(0) < fixed_float(value) by {
        apply(positive_float(value));
        close();
    }
}
```

```expect
pass
```
