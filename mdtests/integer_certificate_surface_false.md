# invalid mathematical Integer certificate

```click
theorem integer_certificate_false(x: Integer) {
    ensures x > x + 1 by {
        integer_certificate {
            trivial => x > x + 1;
            conclusion 0;
        }
    }
}

theorem integer_constant_certificate_false(x: Integer) {
    ensures 1 == 0 by {
        integer_certificate {
            trivial => 1 == 0;
            conclusion 0;
        }
    }
}
```

```expect
fail: integer arithmetic certificate rejected
```
