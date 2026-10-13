# A conversion in range is its operand in a signed certificate

`unsigned char y = x + 1` converts modulo 256, so `y` is `x + 1` only
while `x + 1` is in `0..255`. A `signed_int32` certificate relates the
conversion to its operand with `interval_narrowed_cast`: the operand's
checked interval, here `1..255` from `0 <= x < 255`, must lie inside the
destination range, and the conversion then has that interval and the
operand's affine form. `simp` plans this certificate, and the expansion
below is the one it prints.
`mdtests/a_conversion_one_past_its_range_is_not_its_operand.md` refuses the
same certificate one value wider.

```c filename=a_conversion_in_range_is_its_operand_in_a_signed_certificate.c
int next_byte(int x) { unsigned char y = x + 1; return y; }
```

```click
verifying "a_conversion_in_range_is_its_operand_in_a_signed_certificate.c";
int32 next_byte(int32 x) {
    requires 0 <= x;
    requires x < 255;
    ensures result == x + 1;
} by {
    step();
    step();
    step();
    have result == (x + 1) by {
        arithmetic_certificate signed_int32 {
            premise 0: at(function.entry, x < 255) => at(function.entry, x < 255);
            premise 1: at(function.entry, 0 <= x) => at(function.entry, 0 <= x);
            interval_from_affine 1 (x) (0) (2147483647);
            interval_from_affine 0 (x) (-2147483648) (254);
            interval_intersect 2, 3 (0) (254);
            interval_atom (1) (1) (1);
            interval_add_bounded 4, 5 (1) (255);
            interval_narrowed_cast 6 int32 uint8 (1) (255);
            interval_add_bounded 4, 5 (1) (255);
            trivial => 0 == 0;
            affine_conclusion_pair 9 7 8 => result == (x + 1);
            conclusion 10;
        }
    }
    assumption();
}
```

```expect
pass
```
