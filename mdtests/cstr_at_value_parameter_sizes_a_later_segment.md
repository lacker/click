# A value parameter sizes a later memory clause

`copy_string`'s contract views the source string at a value parameter `n` and
then owns `dst[0..n + 1u64]`, so the destination's size follows the string
the caller passes. `use` holds `cstr_at(src, n)` and owns `n + 1` destination
bytes, which is exactly what the call takes.

```c filename=cstr_at_value_parameter_sizes_a_later_segment.c
void copy_string(uint8 *dst, const uint8 *src);

void use(uint8 *dst, const uint8 *src, uint64 n)
{
	copy_string(dst, src);
}
```

```click
import click::c::string;

verifying "cstr_at_value_parameter_sizes_a_later_segment.c";

extern void copy_string(uint8* dst, const uint8* src) {
    let n: uint64;
    views cstr_at(src, n);
    owns dst[0..n + 1u64];
}

void use(uint8* dst, const uint8* src, uint64 n) {
    views cstr_at(src, n);
    owns dst[0..n + 1u64];
}
```

```expect
pass
```
