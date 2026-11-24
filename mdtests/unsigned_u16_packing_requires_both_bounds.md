# A field that overlaps its neighbor cannot use the packing bridge

```click
import click::integer;

theorem overlapping(low: uint32, high: uint32) {
    requires low <= 65536u32;
    requires high <= 65535u32;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high) by {
        apply(integer::uint32_pack_uint16_to_integer(low, high)); close();
    }
}
```

```expect
fail: low <= 65535u32
```
