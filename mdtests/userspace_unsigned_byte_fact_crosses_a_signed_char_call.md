# An unsigned byte fact crosses a signed char call

A caller knows its byte as `unsigned char` (`q[0] == 200`) and passes it to a
function whose contract reads the same byte as a user-space (signed) `char`.
The callee's guarantee names the call's result by the signed read,
`result == p[0]`, which is the conversion `int8(q[0])` of the caller's
unsigned byte. The caller's `result == -56` follows: the byte's constant
folds through the conversion where the call's guarantee is admitted, just as
it does for any other arithmetic on a known value. Before, the guaranteed
equality held the conversion unfolded and the claim was refused.
`userspace_signed_char_fact_decides_the_unsigned_byte.md` is the reverse
direction.

```c filename=unsigned_byte_fact_crosses_a_signed_char_call.c
int first_char(char *p) {
    return p[0];
}

int first_of_bytes(unsigned char *q) {
    return first_char((char *)q);
}

int first_of_chars(char *p) {
    return first_char(p);
}
```

```click
target "x86_64-linux-userspace";
verifying "unsigned_byte_fact_crosses_a_signed_char_call.c";

int32 first_char(char* p) {
    views p[0..1];
    ensures result == p[0];
} by {
    execute();
    simp();
}

int32 first_of_bytes(uint8* q) {
    views q[0..1];
    requires q[0] == 200;
    ensures result == -56;
} by {
    execute();
    simp();
}

int32 first_of_chars(char* p) {
    views p[0..1];
    requires ((uint8*)p)[0] == 200;
    ensures result == -56;
} by {
    execute();
    simp();
}
```

```expect
pass
```
