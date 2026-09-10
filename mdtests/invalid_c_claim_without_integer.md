# C expression validation without Integer parameters

```click
theorem invalid_c_claim_without_integer() {
    ensures [1u8] < [2u8];
}
```

```expect
fail: sequences support only
```
