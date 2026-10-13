# A nine-bit mask does not make byte narrowing exact

Masking with 511 clears the sign bit but permits values above 255, so the
conversion to `unsigned char` drops the ninth bit: for `value & 511` in
`256..511` the result is 256 less. Claiming the masked word is refused.
`mdtests/masked_uint8_narrowing.md` is the eight-bit mask that is exact.

```c filename=masked_uint8_narrowing.c
unsigned char low_byte(unsigned value) {
    return (unsigned char)(int)(value & 511u);
}
```

```click
verifying "masked_uint8_narrowing.c";
uint8 low_byte(uint32 value) {
    ensures ((uint32)result) == (value & 511u32);
} by { execute(); simp(); }
```

```expect
fail: `ensures ((uint32)result) == (value & 511u32)` failed
```
