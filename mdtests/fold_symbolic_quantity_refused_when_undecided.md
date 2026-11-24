# Folding a symbolic quantity refuses one neither zero nor positive

`k` may be zero or positive, so neither side is provable and the fold is
refused; the proof needs a stronger `requires` or a case split.

```c filename=fold_symbolic_quantity_refused.c
int32 mint(int32 x, int32 k) { return x; }
```

```click
resource ok(x: int32) {
    fact x >= 0;
}

verifying "fold_symbolic_quantity_refused.c";

int32 mint(int32 x, int32 k) {
    requires x >= 0;
    requires 0 <= k;
    produces k of ok(x);
} by {
    step_until(function.exit);
    fold(k of ok(x));
    close();
}
```

```expect
fail: `fold(k of ok(x))` requires its quantity to be proved zero or positive
```
