# A viewed byte range still needs the index inside it

The companion of `mdtests/views_a_byte_range_makes_an_index_readable.md`.
Reading `s[i]` under `views s[0..n]` is defined because `i` is inside the
viewed range, not because the range is viewed. Drop `requires i < n` and the
read is refused, and the refusal names the cell it wanted and the range it
holds in the names the contract wrote them in.

```c filename=views_a_byte_range_still_needs_the_index_bound.c
uint8 read_byte(uint8 s[], int32 i, int32 n) {
    return s[i];
}
```

```click
verifying "views_a_byte_range_still_needs_the_index_bound.c";

uint8 read_byte(uint8 s[], int32 i, int32 n) {
    requires 0 <= i;
    views s[0..n];

}
```

```expect
fail: missing resource fact `views s[i..(i + 1)]`
```
