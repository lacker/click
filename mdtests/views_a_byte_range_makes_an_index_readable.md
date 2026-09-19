# `views` over a byte range makes a symbolic index readable

A `views p[0..n]` clause over an `int32[]` made `p[i]` readable for a symbolic
`i` inside the range, and the same clause over a `uint8[]` did not. The read was
refused with
`the checked execution of 'read_byte' assumed a pure fact at entry, which the contract context cannot derive`,
so a contract that held the range and dropped its redundant
`requires loadable(s[0..n])` stopped verifying for byte buffers only.

The certification rule that answers "does a held resource cover this
loadability fact" recovered the range's element width from the *shape of the
byte extent*: it wanted the product `count * 4`. A range of one-byte elements
has no product left to read. `memory_range_byte_count` folds a factor of one
away, so `s[0..n]` lowers its extent to the bare count `n`, which is
indistinguishable from a byte count that is no element range at all. The width
now comes from the held range, which carries it, and the extent is read back at
that width — an identity at width one, where a byte count already *is* its own
element count.

The three functions below are the three widths that fold differently: one byte
(no product), two bytes (a product the old rule refused because the constant
was not `4`), and a byte range whose start is not `0`.

```c filename=views_a_byte_range_makes_an_index_readable.c
uint8 read_byte(uint8 s[], int32 i, int32 n) {
    return s[i];
}

uint8 read_byte_from(uint8 s[], int32 a, int32 b, int32 i) {
    return s[i];
}

uint16 read_half(uint16 s[], int32 i, int32 n) {
    return s[i];
}
```

```click
verifying "views_a_byte_range_makes_an_index_readable.c";

uint8 read_byte(uint8 s[], int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    views s[0..n];

}

uint8 read_byte_from(uint8 s[], int32 a, int32 b, int32 i) {
    requires 0 <= a;
    requires a <= i;
    requires i < b;
    views s[a..b];

}

uint16 read_half(uint16 s[], int32 i, int32 n) {
    requires 0 <= i;
    requires i < n;
    views s[0..n];

}
```

```expect
pass
```
