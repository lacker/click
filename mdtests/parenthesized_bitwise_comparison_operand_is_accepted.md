# A parenthesized bitwise operand of a comparison is accepted

Parentheses make the grouping explicit, so `(x & 1) == 0` means the same to a
C reader and to Click. An unparenthesized shift operand is accepted because C
and Click group it the same way.

```click
theorem low_bit(x: uint32) {
    requires x == 2u32;
    ensures (x & 1u32) == 0u32 and x << 1u32 == 4u32 by {
        simp();
    }
}
```

```expect
pass
```
