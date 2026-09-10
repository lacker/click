# explicit mathematical Integer certificate

```click
theorem integer_certificate_success(x: Integer) {
    ensures x + 1 > x by {
        integer_certificate {
            trivial => x + 1 > x;
            conclusion 0;
        }
    }
}

theorem integer_constant_certificate(x: Integer) {
    ensures 0 == 0 by {
        integer_certificate {
            trivial => 0 == 0;
            conclusion 0;
        }
    }
}
```

```expect
pass
```
