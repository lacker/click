# A bitwise operand of a comparison needs parentheses

C binds `==` tighter than `&`, `|` and `^`, so in C `x & 1 == 0` means
`x & (1 == 0)`. Click binds comparisons looser than every arithmetic and
bitwise operator, so the same text would mean `(x & 1) == 0`. A comparison
operand whose outermost operator is `&`, `|` or `^` is refused unless it is
parenthesized, so a C reader cannot misread what is proved. Shifts are not
affected: C and Click both read `x << 1 == y` as `(x << 1) == y`.

```click
theorem low_bit(x: uint32) {
    requires x == 2u32;
    ensures x & 1u32 == 0u32 by {
        simp();
    }
}
```

```expect
fail: parenthesize a `&` operand of a comparison
```
