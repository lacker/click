# An unused Integer parameter does not disable C expression validation

```click
theorem invalid_c_claim_with_unused_integer(x: Integer) {
    ensures [1u8] < [2u8];
}
```

```expect
fail: sequences support only
```
