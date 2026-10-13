# A `uint8 *` passed as a `char *` reads signed bytes

GCC and Clang accept passing an `unsigned char *` (`uint8 *`) where a
`char *` is expected with only a `-Wpointer-sign` warning, so Click lowers the
uncast argument exactly as the explicit `(char *)` cast. Under the default
x86_64-linux-userspace target plain `char` is signed, so the callee reads the
byte `0xC8` (200) as `-56`: the conversion reinterprets the bytes rather than
just being accepted. The same holds for an array argument, which decays to
`uint8 *`, and for a `const char *` parameter of a `static inline` callee.

```c filename=a_uint8_pointer_passed_as_a_char_pointer_reads_signed_bytes.c
int first_char(char *p) { return p[0]; }

int pass_pointer(void) {
    uint8 buf[2];
    uint8 *q = buf;
    buf[0] = 200;
    buf[1] = 0;
    return first_char(q);
}

int pass_array(void) {
    uint8 buf[2];
    buf[0] = 200;
    buf[1] = 0;
    return first_char(buf);
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
verifying "a_uint8_pointer_passed_as_a_char_pointer_reads_signed_bytes.c";

int first_char(char *p) {
    views p[0..1];
    ensures result == p[0] by auto;
}
int pass_pointer() { ensures result == -56 by auto; }
int pass_array() { ensures result == -56 by auto; }
int pass_to_inline() { ensures result == -56 by auto; }
```

```expect
pass
```
