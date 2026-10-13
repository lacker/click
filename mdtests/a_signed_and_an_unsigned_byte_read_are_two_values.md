# a signed and an unsigned byte read differ above 0x7F

`s[i]` and `u[i]` read the same byte, once as `signed char` and once as
`unsigned char`. A byte holding `0xFF` is `-1` through `s` and `255` through
`u`, so the two reads are equal only when the byte is below `0x80`, and
`result == 1` is false.

That claim was once **provable**: a load term named the address and the
snapshot but not what was read there, so both reads became one term and
`a == b` was `v == v`. Reads then carried their kind and were two unrelated
terms. They are now related exactly: a byte has one name, its unsigned read,
and a signed read is the two's-complement conversion of that name ("one
byte, one name"). The two values are still different numbers above `0x7F`,
so the claim stays refused; `a_signed_read_of_a_byte_follows_from_its_unsigned_read.md`
shows the relation proving what it should: an unsigned fact decides the signed read.

`a_byte_read_is_not_the_int32_read_at_its_address.md` is the same hole across
widths, and `reads_of_one_kind_at_one_address_stay_equal.md` keeps the reads
that do agree on their kind equal. The note on the C in
`a_byte_store_inside_a_wide_cell_is_not_framed.md` applies to the byte view.

```c filename=a_signed_and_an_unsigned_byte_read_are_two_values.c
int read_both(signed char* s, int i) {
    unsigned char* u;
    int a;
    int b;
    u = (unsigned char*)(void*) s;
    a = s[i];
    b = u[i];
    return a == b;
}
```

```click
verifying "a_signed_and_an_unsigned_byte_read_are_two_values.c";

int read_both(signed char* s, int i) {
    requires i >= 0;
    requires i < 4;
    views s[0..4];
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: `ensures result == 1` failed for `read_both.ensures_0`
```
