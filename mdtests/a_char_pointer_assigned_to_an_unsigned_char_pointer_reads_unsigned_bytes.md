# A `char *` assigned to an `unsigned char *` reads unsigned bytes

GCC and Clang accept initializing an `unsigned char *` or a `signed char *`
from a `char *`, and comparing a `char *` with an `unsigned char *`, with only
a warning (`-Wpointer-sign`, `-Wcompare-distinct-pointer-types`). Click lowers
each uncast conversion exactly as the explicit cast to the destination type.
Under the default x86_64-linux-userspace target the byte stored as the plain
`char` `-56` reads as `200` through the `unsigned char *` and as `-56` through
the `signed char *`.

```c filename=a_char_pointer_assigned_to_an_unsigned_char_pointer_reads_unsigned_bytes.c
int read_unsigned(void) {
    char text[2];
    char *p = text;
    text[0] = -56;
    text[1] = 0;
    unsigned char *q = p;
    return q[0];
}

int read_signed(void) {
    char text[2];
    text[0] = -56;
    text[1] = 0;
    signed char *q = text;
    return q[0];
}

static inline char *identity(char *p) { return p; }

int read_inline_result(void) {
    char text[2];
    text[0] = -56;
    text[1] = 0;
    unsigned char *q;
    q = identity(text);
    return q[0];
}

int same(char *p, unsigned char *q) { return p == q; }
```

```click
verifying "a_char_pointer_assigned_to_an_unsigned_char_pointer_reads_unsigned_bytes.c";

int read_unsigned() { ensures result == 200 by auto; }
int read_signed() { ensures result == -56 by auto; }
int read_inline_result() { ensures result == 200 by auto; }
int same(char *p, unsigned char *q) {
    requires (uint8*)p == q;
    ensures result == 1 by auto;
}
```

```expect
pass
```
