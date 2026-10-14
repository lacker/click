# A cast range bound must be shown to cover the read

A range bound cast to `int32` is C's conversion of the bound, modulo 2^32,
so the range it names can be shorter than the uncast one. Without
`requires length <= 2147483647` nothing shows the converted bound still
covers `bytes[index]`, and the read is refused.

`a_cast_in_a_range_bound_truncates_the_bound.md` states the bound.

```c filename=a_cast_range_bound_must_be_shown_to_cover_the_read.c
unsigned char read(const unsigned char *bytes, unsigned long length, unsigned long index) {
    return bytes[index];
}
```

```click
verifying "a_cast_range_bound_must_be_shown_to_cover_the_read.c";
uint8 read(const uint8* bytes, uint64 length, uint64 index) {
    requires index < length;
    views bytes[0..(int32)length];
    ensures result == bytes[index];
} by { execute(); simp(); }
```

```expect
fail: missing resource fact `views bytes[index]`
```
