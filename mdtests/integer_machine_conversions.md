# Explicit machine and mathematical integer conversions

Conversion preserves the numeric value and the signedness of each machine type.
Unsuffixed literals acquire Integer type from the conversion expression on
either side of a comparison.

```click
theorem integer_conversion_constants() {
    ensures to_integer(-1) == -1 by simp;
    ensures -1 == to_integer(-1) by simp;
    ensures to_integer(4294967295u32) == 4294967295 by simp;
    ensures to_integer(18446744073709551615u64) == 18446744073709551615 by simp;
    ensures to_integer(-1) != to_integer(4294967295u32) by simp;
    ensures to_integer(1) + 18446744073709551615 == 18446744073709551616 by simp;
}

theorem integer_constant_round_trips() {
    ensures to_integer(to_int16(-32768)) == -32768 by simp;
    ensures to_integer(to_int16(32767)) == 32767 by simp;
    ensures to_integer(to_int32(-2147483648)) == -2147483648 by simp;
    ensures to_integer(to_int32(2147483647)) == 2147483647 by simp;
    ensures to_integer(to_uint8(0)) == 0 by simp;
    ensures to_integer(to_uint8(255)) == 255 by simp;
    ensures to_integer(to_uint16(0)) == 0 by simp;
    ensures to_integer(to_uint16(65535)) == 65535 by simp;
    ensures to_integer(to_uint32(0)) == 0 by simp;
    ensures to_integer(to_uint32(4294967295)) == 4294967295 by simp;
    ensures to_integer(to_int64(-9223372036854775808)) == -9223372036854775808 by simp;
    ensures to_integer(to_int64(9223372036854775807)) == 9223372036854775807 by simp;
    ensures to_integer(to_uint64(0)) == 0 by simp;
    ensures to_integer(to_uint64(18446744073709551615)) == 18446744073709551615 by simp;
}

theorem typed_integer_observations(a: int16, b: uint8, c: uint16,
        d: int32, e: uint32, f: int64, g: uint64) {
    ensures to_integer(a) == to_integer(a) by simp;
    ensures to_integer(b) == to_integer(b) by simp;
    ensures to_integer(c) == to_integer(c) by simp;
    ensures to_integer(d) == to_integer(d) by simp;
    ensures to_integer(e) == to_integer(e) by simp;
    ensures to_integer(f) == to_integer(f) by simp;
    ensures to_integer(g) == to_integer(g) by simp;
}
```

```expect
pass
```
