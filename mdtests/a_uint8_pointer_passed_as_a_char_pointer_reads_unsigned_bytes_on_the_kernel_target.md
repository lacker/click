# A `uint8 *` passed as a `char *` reads unsigned bytes on the kernel target

The x86_64-linux-kernel form of
`a_uint8_pointer_passed_as_a_char_pointer_reads_signed_bytes.md`. Plain `char`
is unsigned there, so the uncast `uint8 *` to `char *` argument, lowered as
the explicit `(char *)` cast, reads the byte `0xC8` as `200`.

```c filename=a_uint8_pointer_passed_as_a_char_pointer_reads_unsigned_bytes_on_the_kernel_target.c
int first_char(char *p) { return p[0]; }

int pass_pointer(void) {
    uint8 buf[2];
    uint8 *q = buf;
    buf[0] = 200;
    buf[1] = 0;
    return first_char(q);
}

static inline int inline_first(const char *p) { return p[0]; }

int pass_to_inline(void) {
    uint8 buf[2];
    buf[0] = 200;
    buf[1] = 0;
    return inline_first(buf);
}
```

```click
target "x86_64-linux-kernel";
verifying "a_uint8_pointer_passed_as_a_char_pointer_reads_unsigned_bytes_on_the_kernel_target.c";

int first_char(char *p) {
    views p[0..1];
    ensures result == p[0] by auto;
}
int pass_pointer() { ensures result == 200 by auto; }
int pass_to_inline() { ensures result == 200 by auto; }
```

```expect
pass
```
