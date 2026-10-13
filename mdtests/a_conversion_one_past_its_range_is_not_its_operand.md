# A conversion one past its range is not its operand

With `0 <= x < 256` the operand `x + 1` reaches 256, which `unsigned char`
holds as 0, so the conversion is not `x + 1`. The certificate of
`mdtests/a_conversion_in_range_is_its_operand_in_a_signed_certificate.md`,
widened by one value, is refused at its `interval_narrowed_cast` node.

```c filename=a_conversion_one_past_its_range_is_not_its_operand.c
int next_byte(int x) { unsigned char y = x + 1; return y; }
```

```click
verifying "a_conversion_one_past_its_range_is_not_its_operand.c";
int32 next_byte(int32 x) {
    requires 0 <= x;
    requires x < 256;
    ensures result == x + 1;
} by {
    step();
    step();
    step();
    have result == (x + 1) by {
        arithmetic_certificate signed_int32 {
            premise 0: at(function.entry, x < 256) => at(function.entry, x < 256);
            premise 1: at(function.entry, 0 <= x) => at(function.entry, 0 <= x);
            interval_from_affine 1 (x) (0) (2147483647);
            interval_from_affine 0 (x) (-2147483648) (255);
            interval_intersect 2, 3 (0) (255);
            interval_atom (1) (1) (1);
            interval_add_bounded 4, 5 (1) (256);
            interval_narrowed_cast 6 int32 uint8 (1) (256);
            interval_add_bounded 4, 5 (1) (256);
            trivial => 0 == 0;
            affine_conclusion_pair 9 7 8 => result == (x + 1);
            conclusion 10;
        }
    }
    assumption();
}
```

```expect
fail: node 7 has an invalid interval endpoint
```
