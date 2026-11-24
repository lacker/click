# Swapping Integer equality operands does not change its polarity

```click
theorem equal_arguments(a: Integer, b: Integer) {
    requires a == b;
    ensures a == b by close();
}

theorem unequal_arguments(a: Integer, b: Integer) {
    requires b != a;
    ensures a == b by {
        apply(equal_arguments(a, b));
    }
}
```

```expect
fail: theorem `equal_arguments` has an unproved obligation
```
