# A user-space string literal is `char` storage read as bytes too

A string literal's elements are plain `char` (C11 6.4.5p6), so under the
user-space target the literal `"\xc8"` holds a `char` of value -56. Click's
byte-string extension still passes a literal itself where `unsigned char`
bytes are read: the read sees the same byte, 200.

```c filename=literal_bytes.c
int first_byte(const unsigned char *bytes) {
    return bytes[0];
}

int as_bytes(void) {
    return first_byte("\xc8");
}

int as_char(void) {
    const char *s = "\xc8";
    return s[0];
}
```

```click
target "x86_64-linux-userspace";
verifying "literal_bytes.c";

int32 first_byte(const uint8* bytes) {
    views bytes[0..1];
    ensures result == bytes[0];
} by {
    execute();
    simp();
}

int32 as_bytes() {
    ensures result == 200;
} by {
    execute();
    simp();
}

int32 as_char() {
    ensures result == -56;
} by {
    execute();
    simp();
}
```

```expect
pass
```
