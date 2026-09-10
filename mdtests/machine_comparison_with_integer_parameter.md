# A mathematical parameter does not change machine comparisons

Contextual numeral spelling must preserve the C domain when the other operand
is a C value. Both theorems check the same machine comparison.

```click
theorem machine_bound(x: int32) {
    requires x >= 0;
    ensures x >= 0 by { assumption(); }
}

theorem machine_bound_with_integer(x: int32, unused: Integer) {
    requires x >= 0;
    ensures x >= 0 by { assumption(); }
}
```

```expect
pass
```
