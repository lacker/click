# Division rounds to the integer bound and no further

`2 * x <= 5` gives `x <= 2` over the integers. Claiming the stronger
`x <= 1` from the same division is refused.

```click
theorem over_rounded(x: Integer) {
    requires 2 * x <= 5;
    ensures x <= 1 by {
        arithmetic_certificate {
            premise 0: 2 * x <= 5 => 2 * x <= 5;
            divide 0 by 2 => x <= 1;
            conclusion 1;
        }
    }
}
```

```expect
fail: node 1 does not state what its rule derives from its inputs
```
