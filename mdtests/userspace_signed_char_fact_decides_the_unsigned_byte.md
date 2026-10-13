# A signed char fact decides the unsigned byte

One byte, one name: a byte's single term is its unsigned read, and a signed
`char` read of it is the two's-complement conversion of that term. The
conversion is a bijection from `0..255` onto `-128..127`, so a fact about
the signed read decides the unsigned one: `p[0] == 7` gives
`((unsigned char *)p)[0] == 7`, and `p[0] == -56` gives `200`. The
contracts here state the byte as a user-space (signed) `char` and the bodies
read it through an `unsigned char *` view. Both `simp` and its checked
expansion use the same rule, in a returned value, a branch condition, and a
callee's `unsigned char` precondition.
`userspace_signed_char_fact_does_not_give_another_unsigned_byte.md` keeps
the refusals of other values, and
`a_signed_read_of_a_byte_follows_from_its_unsigned_read.md` is the other
direction.

```c filename=signed_char_fact_decides_the_unsigned_byte.c
int first_unsigned(char *p) {
    return ((unsigned char *)p)[0];
}

int is_high(char *p) {
    if (((unsigned char *)p)[0] == 0xC8) {
        return 1;
    }
    return 0;
}

int need_seven(unsigned char *u) {
    return u[0];
}

int pass_seven(char *p) {
    return need_seven((unsigned char *)p);
}
```

```click
target "x86_64-linux-userspace";
verifying "signed_char_fact_decides_the_unsigned_byte.c";

int32 first_unsigned(char* p) {
    views p[0..1];
    requires p[0] == 7;
    ensures result == 7;
} by {
    execute();
    simp();
}

int32 is_high(char* p) {
    views p[0..1];
    requires p[0] == -56;
    ensures result == 1;
} by {
    execute();
    simp();
}

int32 need_seven(uint8* u) {
    views u[0..1];
    requires u[0] == 7;
    ensures result == 7;
} by {
    execute();
    simp();
}

int32 pass_seven(char* p) {
    views p[0..1];
    requires p[0] == 7;
    ensures result == 7;
} by {
    execute();
    simp();
}
```

```expect
pass
```
