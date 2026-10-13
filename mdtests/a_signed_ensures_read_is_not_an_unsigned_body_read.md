# a signed ensures read is not an unsigned body read

The body reads the byte through `unsigned char*`; the contract reads it
through the `signed char*` parameter. For a byte of `0xFF` the body returns
`255` and `s[i]` is `-1`, so `result == s[i]` is false.

The claim was **provable**: the contract's `s[i]` and the body's `u[i]` named
one load term, so the equality closed by normalization alone. A load term now
carries the width and signedness of its read, and the refusal names that as
the difference.

```c filename=a_signed_ensures_read_is_not_an_unsigned_body_read.c
int read_unsigned(signed char* s, int i) {
    unsigned char* u;
    u = (unsigned char*)(void*) s;
    return u[i];
}
```

```click
verifying "a_signed_ensures_read_is_not_an_unsigned_body_read.c";

int read_unsigned(signed char* s, int i) {
    requires i >= 0;
    requires i < 4;
    views s[0..4];
    ensures result == s[i];
} by {
    execute();
    simp();
}
```

```expect
fail: They read the same byte, and its signed value is its unsigned value only when the byte is below 0x80
```
