# explicit signed int32 arithmetic certificate

```click
theorem signed_int32_certificate_surface(x: int32) {
    requires x <= 1;
    ensures x <= 1 by {
        arithmetic_certificate signed_int32 {
            premise 0: x <= 1 => x <= 1;
            conclusion 0;
        }
    }
}
```

```expect
pass
```
