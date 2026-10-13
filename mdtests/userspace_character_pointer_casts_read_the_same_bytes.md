# User-space character pointer casts read the same bytes

C11 6.3.2.3p7 and 6.5p7 let a character pointer of any kind view an
object's bytes. Under the user-space target plain `char` is signed, so a
`char *` and a `signed char *` read the same `int8` value, while an
`unsigned char *` reads the same byte as its unsigned value. The casts are
one-level conversions between character pointer types; none retypes a
non-character object.

```c filename=character_casts.c
int as_signed(char *p) {
    signed char *s = (signed char *)p;
    return s[0];
}

int as_unsigned(char *p) {
    unsigned char *u = (unsigned char *)p;
    return u[0];
}

int back_to_char(unsigned char *u) {
    char *p = (char *)u;
    return p[0];
}
```

```click
target "x86_64-linux-userspace";
verifying "character_casts.c";

int32 as_signed(char* p) {
    views p[0..1];
    requires p[0] == -56;
    ensures result == -56;
} by {
    execute();
    simp();
}

int32 as_unsigned(char* p) {
    views p[0..1];
    requires ((uint8*)p)[0] == 200;
    ensures result == 200;
} by {
    execute();
    simp();
}

int32 back_to_char(uint8* u) {
    views u[0..1];
    requires u[0] == 200;
    ensures result == -56;
} by {
    execute();
    simp();
}
```

```expect
pass
```
