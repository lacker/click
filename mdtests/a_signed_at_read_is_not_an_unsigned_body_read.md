# a signed at read is not an unsigned body read

`at(function.entry, s[i])` reads the byte at entry as `signed char`; the body
read it as `unsigned char`. Nothing writes the byte, so the snapshots agree,
and the two reads still differ for every byte of `0x80` or more.

The claim was **provable** for the same reason as
`a_signed_ensures_read_is_not_an_unsigned_body_read.md`: an `at(...)` read
named the same load term as the body's read of another kind.

```c filename=a_signed_at_read_is_not_an_unsigned_body_read.c
int read_unsigned(signed char* s, int i) {
    unsigned char* u;
    int b;
    u = (unsigned char*)(void*) s;
    b = u[i];
    return b;
}
```

```click
verifying "a_signed_at_read_is_not_an_unsigned_body_read.c";

int read_unsigned(signed char* s, int i) {
    requires i >= 0;
    requires i < 4;
    views s[0..4];
    ensures result == at(function.entry, s[i]);
} by {
    execute();
    simp();
}
```

```expect
fail: They read the same byte, and its signed value is its unsigned value only when the byte is below 0x80
```
