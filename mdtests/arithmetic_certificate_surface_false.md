# invalid mathematical Integer certificate

```click
theorem arithmetic_certificate_false(x: Integer) {
    ensures x > x + 1 by {
        arithmetic_certificate {
            trivial => x > x + 1;
            conclusion 0;
        }
    }
}

theorem integer_constant_certificate_false(x: Integer) {
    ensures 1 == 0 by {
        arithmetic_certificate {
            trivial => 1 == 0;
            conclusion 0;
        }
    }
}
```

```expect
fail: integer arithmetic certificate rejected
```
